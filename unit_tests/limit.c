#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/resource.h>
#include <sys/time.h>
#include <sys/wait.h>

void usage() {
  fprintf(stderr, "limit [-m MB] [-c SEC] [-w SEC] [-f KB] -x \"CMD\"\n");
  fprintf(stderr, "  -m  total memory\n");
  fprintf(stderr, "  -c  CPU time\n");
  fprintf(stderr, "  -w  wall-clock time\n");
  fprintf(stderr, "  -f  output file size\n");
  fprintf(stderr, "  -x  the command to execute\n");
  exit(1);
}

/*
 * Exit codes:
 *  0 - everything went OK (might be CPU, MEM, or FILE limit exceeded!)
 *  1 - I was not invoked correctly
 *  2 - I can't fork
 *  3 - I can't execute
 *  4 - wall time expired, I had to abort
 *  5 - child retuned nonzero exit code
 */
int main(int argc, char* argv[]) {
  int i;
  int child;
  int status;
  int tle;
  struct rlimit cpu, mem, file, fcnt;
  int wall;
  struct timeval start_time, current_time;
  char* cmd;
  int sec, usec; // elapsed wall time

  /* defaults */
  wall = 180;               // 3 minutes
  cpu.rlim_cur = 60;        // 1 minute
  mem.rlim_cur = 512;       // half a giga
  file.rlim_cur = 1 << 14;  // 16 MB
  fcnt.rlim_cur = fcnt.rlim_max = 128; // no need for more open files

  /* parse arguments */
  if (!(argc&1)) usage();
  cmd = NULL;
  for (i = 1; i + 1 < argc; i += 2) {
    if (!strcmp("-m", argv[i])) sscanf(argv[i+1], "%d", (int*)&mem.rlim_cur);
    else if (!strcmp("-c", argv[i])) sscanf(argv[i+1], "%d", (int*)&cpu.rlim_cur);
    else if (!strcmp("-w", argv[i])) sscanf(argv[i+1], "%d", &wall);
    else if (!strcmp("-f", argv[i])) sscanf(argv[i+1], "%d", (int*)&file.rlim_cur);
    else if (!strcmp("-x", argv[i])) cmd = argv[i+1];
    else usage();
  }
  if (cmd == NULL) usage();
  if (wall > cpu.rlim_cur) wall = cpu.rlim_cur;
  mem.rlim_cur <<= 20;  // MB
  file.rlim_cur <<= 10; // KB
  cpu.rlim_max = cpu.rlim_cur;
  mem.rlim_max = mem.rlim_cur;
  file.rlim_max = file.rlim_cur;

  /* set limits */
  setrlimit(RLIMIT_CPU, &cpu);
  setrlimit(RLIMIT_AS, &mem);
  setrlimit(RLIMIT_FSIZE, &file);
  setrlimit(RLIMIT_NOFILE, &fcnt);

  /* start the child */
  child = fork();
  if (child == -1) {
    fprintf(stderr, "can't fork.");
    return 2;
  }
  if (child == 0) {
    setsid();
    execl("/bin/sh", "sh", "-c", cmd, (char*)0);
    perror("Can't execute");
    return 3;
  }

  /* watch out for wall time limit */
  gettimeofday(&start_time, NULL);
  while (!waitpid(child, &status, WNOHANG)) {
    usleep(25000);
    gettimeofday(&current_time, NULL);
    sec = current_time.tv_sec - start_time.tv_sec;
    usec = current_time.tv_usec - start_time.tv_usec;
    if (sec > wall || (sec == wall && usec > 0)) {
      fprintf(stderr, "Hanged\n");
      if (killpg(child, SIGKILL))
        fprintf(stderr, "Failed to kill");
    }
    usleep(50000);
  }
  if (WIFSIGNALED(status)) return 4;
  if (WEXITSTATUS(status)) {
    fprintf(stderr, "EXIT CODE %d\n", WEXITSTATUS(status));
    return 5;
  }
  return 0;
}
