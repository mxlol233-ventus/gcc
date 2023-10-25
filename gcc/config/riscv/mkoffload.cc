/* Offload image generation tool for ventus-gpgpu.
   Copyright (C) 2023 Free Software Foundation, Inc.
   This file is part of GCC.
   GCC is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 3, or (at your option)
   any later version.
   GCC is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.
   Under Section 7 of GPL version 3, you are granted additional
   permissions described in the GCC Runtime Library Exception, version
   3.1, as published by the Free Software Foundation.
   You should have received a copy of the GNU General Public License and
   a copy of the GCC Runtime Library Exception along with this program;
   see the files COPYING3 and COPYING.RUNTIME respectively.  If not, see
   <http://www.gnu.org/licenses/>.  */

#include "collect-utils.h"
#include "config.h"
#include "coretypes.h"
#include "diagnostic.h"
#include "elf.h"
#include "gomp-constants.h"
#include "intl.h"
#include "obstack.h"
#include "simple-object.h"
#include "system.h"
#include <elf.h>
#include <libgen.h>
#include <stdio.h>

const char tool_name[] = "ventus mkoffload";

static const char *gcn_dumpbase;
static struct obstack files_to_cleanup;
enum offload_abi offload_abi = OFFLOAD_ABI_UNSET;

void tool_cleanup(bool from_signal) {}

static void mkoffload_cleanup(void) { tool_cleanup(false); }

static int access_check(const char *name, int mode) {
  if (mode == X_OK) {
    struct stat st;

    if (stat(name, &st) < 0 || S_ISDIR(st.st_mode))
      return -1;
  }

  return access(name, mode);
}

static unsigned parse_env_var(const char *str, char ***pvalues) {
  const char *curval, *nextval;
  char **values;
  unsigned num = 1, i;

  curval = strchr(str, ':');
  while (curval) {
    num++;
    curval = strchr(curval + 1, ':');
  }

  values = (char **)xmalloc(num * sizeof(char *));
  curval = str;
  nextval = strchr(curval, ':');
  if (nextval == NULL)
    nextval = strchr(curval, '\0');

  for (i = 0; i < num; i++) {
    int l = nextval - curval;
    values[i] = (char *)xmalloc(l + 1);
    memcpy(values[i], curval, l);
    values[i][l] = 0;
    curval = nextval + 1;
    nextval = strchr(curval, ':');
    if (nextval == NULL)
      nextval = strchr(curval, '\0');
  }
  *pvalues = values;
  return num;
}

static void free_array_of_ptrs(void **ptr, unsigned n) {
  unsigned i;
  if (!ptr)
    return;
  for (i = 0; i < n; i++) {
    if (!ptr[i])
      break;
    free(ptr[i]);
  }
  free(ptr);
  return;
}

static void xputenv(const char *string) {
  if (verbose)
    fprintf(stderr, "%s\n", string);
  putenv(CONST_CAST(char *, string));
}

static bool copy_early_debug_info(const char *infile, const char *outfile) {
  const char *errmsg;
  int err;

  /* The simple_object code can handle extracting the debug sections.
     This code is based on that in lto-wrapper.cc.  */
  int infd = open(infile, O_RDONLY | O_BINARY);
  if (infd == -1)
    return false;
  simple_object_read *inobj =
      simple_object_start_read(infd, 0, "__GNU_LTO", &errmsg, &err);
  if (!inobj)
    return false;

  off_t off, len;
  if (simple_object_find_section(inobj, ".gnu.debuglto_.debug_info", &off, &len,
                                 &errmsg, &err) != 1) {
    simple_object_release_read(inobj);
    close(infd);
    return false;
  }

  errmsg = simple_object_copy_lto_debug_sections(inobj, outfile, &err, true);
  if (errmsg) {
    unlink_if_ordinary(outfile);
    return false;
  }

  simple_object_release_read(inobj);
  close(infd);

  /* Open the file we just created for some adjustments.
     The simple_object code can't do this, so we do it manually.  */
  FILE *outfd = fopen(outfile, "r+b");
  if (!outfd)
    return false;

  // Elf64_Ehdr: The Elf file HeaDeR is located at the beginning of the file,
  // and is used to locate the other parts of the file.
  Elf64_Ehdr ehdr;
  if (fread(&ehdr, sizeof(ehdr), 1, outfd) != 1) {
    fclose(outfd);
    return true;
  }

  gcc_assert(ehdr.e_machine == EM_X86_64);

  /* Load the section headers so we can walk them later.  */
  Elf64_Shdr *sections =
      (Elf64_Shdr *)xmalloc(sizeof(Elf64_Shdr) * ehdr.e_shnum);
  if (fseek(outfd, ehdr.e_shoff, SEEK_SET) == -1 ||
      fread(sections, sizeof(Elf64_Shdr), ehdr.e_shnum, outfd) !=
          ehdr.e_shnum) {
    free(sections);
    fclose(outfd);
    return true;
  }

  for (int i = 0; i < ehdr.e_shnum; i++) {
    if (sections[i].sh_type != SHT_RELA)
      continue;

    char *data = (char *)xmalloc(sections[i].sh_size);
    if (fseek(outfd, sections[i].sh_offset, SEEK_SET) == -1 ||
        fread(data, sections[i].sh_size, 1, outfd) != 1) {
      free(data);
      continue;
    }

    for (size_t offset = 0; offset < sections[i].sh_size;
         offset += sections[i].sh_entsize) {
      Elf64_Rela *reloc = (Elf64_Rela *)(data + offset);

      // switch (ELF64_R_TYPE (reloc->r_info))
      //   {
      //   case R_X86_64_32:
      //   case R_X86_64_32S:
      //     reloc->r_info
      // = ELF32_R_INFO (ELF32_R_SYM (reloc->r_info), R_RISCV_);
      //     break;
      //   case R_X86_64_PC32:
      //     reloc->r_info
      // = ELF32_R_INFO (ELF32_R_SYM (reloc->r_info), R_RISCV_REL);
      //     break;
      //   case R_X86_64_PC64:
      //     reloc->r_info
      // = ELF32_R_INFO (ELF32_R_SYM (reloc->r_info), R_AMDGPU_REL64);
      //     break;
      //   case R_X86_64_64:
      //     reloc->r_info
      // = ELF32_R_INFO (ELF32_R_SYM (reloc->r_info), R_AMDGPU_ABS64);
      //     break;
      //   case R_X86_64_RELATIVE:
      //     reloc->r_info
      // = ELF32_R_INFO (ELF32_R_SYM (reloc->r_info), R_RISCV_RELATIVE);
      //     break;
      //   default:
      //     gcc_unreachable ();
      //   }
    }
  }

  return true;
}

int main(int argc, char **argv) {
  printf("hello ventus!\n");

  FILE *in = stdin;
  FILE *out = stdout;
  FILE *cfile = stdout;
  const char *outname = 0;

  progname = tool_name;
  diagnostic_initialize(global_dc, 0);

  obstack_init(&files_to_cleanup);
  if (atexit(mkoffload_cleanup) != 0)
    fatal_error(input_location, "atexit failed");

  char *collect_gcc = getenv("COLLECT_GCC");
  if (collect_gcc == NULL)
    fatal_error(input_location, "COLLECT_GCC must be set.");
  const char *gcc_path = dirname(ASTRDUP(collect_gcc));
  const char *gcc_exec = basename(ASTRDUP(collect_gcc));

  size_t len = (strlen(gcc_path) + 1 + strlen(GCC_INSTALL_NAME) + 1);
  char *driver = XALLOCAVEC(char, len);

  if (strcmp(gcc_exec, collect_gcc) == 0)
    /* collect_gcc has no path, so it was found in PATH.  Make sure we also
       find accel-gcc in PATH.  */
    gcc_path = NULL;

  int driver_used = 0;
  if (gcc_path != NULL)
    driver_used = sprintf(driver, "%s/", gcc_path);
  sprintf(driver + driver_used, "%s", GCC_INSTALL_NAME);

  bool found = false;
  if (gcc_path == NULL)
    found = true;
  else if (access_check(driver, X_OK) == 0)
    found = true;
  else {
    /* Don't use alloca pointer with XRESIZEVEC.  */
    driver = NULL;
    /* Look in all COMPILER_PATHs for GCC_INSTALL_NAME.  */
    char **paths = NULL;
    unsigned n_paths;
    n_paths = parse_env_var(getenv("COMPILER_PATH"), &paths);
    for (unsigned i = 0; i < n_paths; i++) {
      len = strlen(paths[i]) + 1 + strlen(GCC_INSTALL_NAME) + 1;
      driver = XRESIZEVEC(char, driver, len);
      sprintf(driver, "%s/%s", paths[i], GCC_INSTALL_NAME);
      if (access_check(driver, X_OK) == 0) {
        found = true;
        break;
      }
    }
    free_array_of_ptrs((void **)paths, n_paths);
  }

  if (!found)
    fatal_error(input_location, "offload compiler %s not found",
                GCC_INSTALL_NAME);

  expandargv(&argc, &argv);

  /* Scan the argument vector.  */
  bool fopenmp = false;
  bool fopenacc = false;
  bool fPIC = false;
  bool fpic = false;
  for (int i = 1; i < argc; i++) {
#define STR "-foffload-abi="
    if (startswith(argv[i], STR)) {
      if (strcmp(argv[i] + strlen(STR), "lp64") == 0)
        offload_abi = OFFLOAD_ABI_LP64;
      else if (strcmp(argv[i] + strlen(STR), "ilp32") == 0)
        offload_abi = OFFLOAD_ABI_ILP32;
      else
        fatal_error(input_location, "unrecognizable argument of option " STR);
    }
#undef STR
    else if (strcmp(argv[i], "-fopenmp") == 0)
      fopenmp = true;
    else if (strcmp(argv[i], "-fopenacc") == 0)
      fopenacc = true;
    else if (strcmp(argv[i], "-fPIC") == 0)
      fPIC = true;
    else if (strcmp(argv[i], "-fpic") == 0)
      fpic = true;
    else if (strcmp(argv[i], "-save-temps") == 0)
      save_temps = true;
    else if (strcmp(argv[i], "-v") == 0)
      verbose = true;
    else if (strcmp(argv[i], "-dumpbase") == 0 && i + 1 < argc)
      dumppfx = argv[++i];
  }

  if (!(fopenacc ^ fopenmp))
    fatal_error(input_location, "either -fopenacc or -fopenmp must be set");

  const char *abi;
  switch (offload_abi) {
  case OFFLOAD_ABI_LP64:
    abi = "-mabi=lp64d";
    break;
  case OFFLOAD_ABI_ILP32:
    abi = "-mabi=ipl32d";
    break;
  default:
    gcc_unreachable();
  }

  /* Build arguments for compiler pass.  */
  struct obstack cc_argv_obstack;
  obstack_init(&cc_argv_obstack);
  obstack_ptr_grow(&cc_argv_obstack, driver);
  obstack_ptr_grow(&cc_argv_obstack, "-S");

  if (save_temps)
    obstack_ptr_grow(&cc_argv_obstack, "-save-temps");
  if (verbose)
    obstack_ptr_grow(&cc_argv_obstack, "-v");
  obstack_ptr_grow(&cc_argv_obstack, abi);
  obstack_ptr_grow(&cc_argv_obstack, "-xlto");
  if (fopenmp)
    obstack_ptr_grow(&cc_argv_obstack, "-mgomp");

  for (int ix = 1; ix != argc; ix++) {
    if (!strcmp(argv[ix], "-o") && ix + 1 != argc)
      outname = argv[++ix];
    else
      obstack_ptr_grow(&cc_argv_obstack, argv[ix]);
  }

  if (!dumppfx)
    dumppfx = outname;

  gcn_dumpbase = concat(dumppfx, ".c", NULL);

  const char *gcn_cfile_name;
  if (save_temps)
    gcn_cfile_name = gcn_dumpbase;
  else
    gcn_cfile_name = make_temp_file(".c");
  obstack_ptr_grow(&files_to_cleanup, gcn_cfile_name);

  cfile = fopen(gcn_cfile_name, "w");
  if (!cfile)
    fatal_error(input_location, "cannot open '%s'", gcn_cfile_name);

  if (offload_abi == OFFLOAD_ABI_LP64) {
    const char *mko_dumpbase = concat(dumppfx, ".mkoffload", NULL);

    const char *gcn_s1_name;
    const char *gcn_s2_name;
    const char *gcn_o_name;

    if (save_temps) {
      gcn_s1_name = concat(mko_dumpbase, ".1.s", NULL);
      gcn_s2_name = concat(mko_dumpbase, ".2.s", NULL);
    } else {
      gcn_s1_name = make_temp_file(".mkoffload.1.s");
      gcn_s2_name = make_temp_file(".mkoffload.2.s");
    }

    obstack_ptr_grow(&files_to_cleanup, gcn_s1_name);
    obstack_ptr_grow(&files_to_cleanup, gcn_s2_name);
    obstack_ptr_grow(&files_to_cleanup, gcn_o_name);

    obstack_ptr_grow(&cc_argv_obstack, "-dumpdir");
    obstack_ptr_grow(&cc_argv_obstack, "");
    obstack_ptr_grow(&cc_argv_obstack, "-dumpbase");
    obstack_ptr_grow(&cc_argv_obstack, mko_dumpbase);
    obstack_ptr_grow(&cc_argv_obstack, "-dumpbase-ext");
    obstack_ptr_grow(&cc_argv_obstack, "");

    obstack_ptr_grow(&cc_argv_obstack, "-o");
    obstack_ptr_grow(&cc_argv_obstack, gcn_s1_name);
    obstack_ptr_grow(&cc_argv_obstack, NULL);
    const char **cc_argv = XOBFINISH(&cc_argv_obstack, const char **);

    struct obstack ld_argv_obstack;
    obstack_init(&ld_argv_obstack);
    obstack_ptr_grow(&ld_argv_obstack, driver);

    int dbgcount = 0;
    for (int ix = 1; ix != argc; ix++) {
      if (!strcmp(argv[ix], "-o") && ix + 1 != argc)
        ++ix;
      else {
        if (strcmp(argv[ix] + strlen(argv[ix]) - 2, ".o") == 0) {
          char *dbgobj;
          if (save_temps) {
            char buf[10];
            sprintf(buf, "%d", dbgcount++);
            dbgobj = concat(dumppfx, ".mkoffload.dbg", buf, ".o", NULL);
          } else
            dbgobj = make_temp_file(".mkoffload.dbg.o");

          obstack_ptr_grow(&files_to_cleanup, dbgobj);

          if (copy_early_debug_info(argv[ix], dbgobj)) {
            obstack_ptr_grow(&ld_argv_obstack, dbgobj);
            obstack_ptr_grow(&files_to_cleanup, dbgobj);
          } else
            free(dbgobj);
        }
      }
    }

    if (verbose)
      obstack_ptr_grow(&ld_argv_obstack, "-v");

    if (save_temps)
      obstack_ptr_grow(&ld_argv_obstack, "-save-temps");

    for (int i = 1; i < argc; i++)
      if (startswith(argv[i], "-l") || startswith(argv[i], "-Wl") ||
          startswith(argv[i], "-march"))
        obstack_ptr_grow(&ld_argv_obstack, argv[i]);

    obstack_ptr_grow(&cc_argv_obstack, "-dumpdir");
    obstack_ptr_grow(&cc_argv_obstack, "");
    obstack_ptr_grow(&cc_argv_obstack, "-dumpbase");
    obstack_ptr_grow(&cc_argv_obstack, "-dumpbase-ext");
    obstack_ptr_grow(&cc_argv_obstack, "");

    obstack_ptr_grow(&ld_argv_obstack, "-o");
    obstack_ptr_grow(&ld_argv_obstack, gcn_o_name);
    obstack_ptr_grow(&ld_argv_obstack, NULL);
    const char **ld_argv = XOBFINISH(&ld_argv_obstack, const char **);

    /* Clean up unhelpful environment variables.  */
    char *execpath = getenv("GCC_EXEC_PREFIX");
    char *cpath = getenv("COMPILER_PATH");
    char *lpath = getenv("LIBRARY_PATH");
    unsetenv("GCC_EXEC_PREFIX");
    unsetenv("COMPILER_PATH");
    unsetenv("LIBRARY_PATH");

    char *omp_requires_file;
    if (save_temps)
      omp_requires_file = concat(dumppfx, ".mkoffload.omp_requires", NULL);
    else
      omp_requires_file = make_temp_file(".mkoffload.omp_requires");
    obstack_ptr_grow(&files_to_cleanup, omp_requires_file);

    /* Run the compiler pass.  */
    xputenv(concat("GCC_OFFLOAD_OMP_REQUIRES_FILE=", omp_requires_file, NULL));
    fork_execute(cc_argv[0], CONST_CAST(char **, cc_argv), true, ".gcc_args");
    obstack_free(&cc_argv_obstack, NULL);
    unsetenv("GCC_OFFLOAD_OMP_REQUIRES_FILE");
  }

  return -1;
}
