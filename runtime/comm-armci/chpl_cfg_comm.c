#include <mpi.h>
#include <armci.h>
#include <gpc.h>

#include <stdio.h> // for sprintf()
#include <stdint.h>
#include <string.h>
#include <strings.h>

#include "chplcomm.h"
#include "chplmem.h"
#include "chplrt.h"
#include "error.h"

#define MEG (1024 * 1024)
#define _MAX_ARMCI_MEMSZ (64 * MEG)

// Undefine this symbol to deactivate extra runtime error checking
#define _ARMCI_DEBUG

#ifdef _ARMCI_DEBUG
#define ARMCI_SAFE(fncall)                                 \
{                                                          \
  int ret;                                                 \
  char buff[256];                                          \
                                                           \
  ret = fncall;                                            \
  if (ret != 0) {                                          \
    sprintf(buff, "ARMCI function call error: %d %s %d\n", \
            ret, __FILE__, __LINE__);                      \
    ARMCI_Error(buff, ret);                                \
  }                                                        \
}
#else
#define ARMCI_SAFE(fncall) fncall
#endif

#ifdef _ARMCI_DEBUG
#define MPI_SAFE(fncall)                              \
{                                                     \
  char errmsg[MPI_MAX_ERROR_STRING];                  \
  int len;                                            \
  int ret;                                            \
                                                      \
  ret = fncall;                                       \
  if (ret != MPI_SUCCESS) {                           \
    MPI_Error_string(ret, errmsg, &len);              \
    chpl_internal_error("MPI error:");                \
    chpl_internal_error(errmsg);                      \
    MPI_Abort(MPI_COMM_WORLD, ret);                   \
  }                                                   \
}
#else
#define MPI_SAFE(fncall) fncall
#endif

typedef struct {
  int               caller;
  chpl_bool         serial_state; // whether the current thread is allowed to spawn new threads
  chpl_fn_int_t     fid;
  chpl_bool         block; // whether the fork is blocking or not
  int               arg_size;
  char              arg[0];       // variable-sized data here
} dist_fork_t;

typedef struct {
  dist_fork_t *info; // Input data
  int *rhdr; // completion signal data
} gpc_info_t;

static int gpc_call_handler(int to, int from, void *hdr, int hlen,
                            void *data,  int dlen,
                            void *rhdr,  int rhlen, int *rhsize,
                            void *rdata, int rdlen, int *rdsize,
                            int rtype);
static int ghndl = -1;
static chpl_mutex_t armci_lock;

int32_t chpl_comm_getMaxThreads(void) {
  return 0; // set to 0 assuming ARMCI does not limit the number of
            // threads that can be running on a process
}

int32_t chpl_comm_maxThreadsLimit(void) {
  return 0; // set to 0 assuming ARMCI does not limit the number of
            // threads that can be running on a process
}

//
// initializes the communications package
//   set chpl_localeID and chpl_numLocales
// notes:
//   * For a user invocation of main(), this routine is called with
//     the argc/argv pair generated by chpl_comm_create_argcv
//   * For a comm-layer invocation of main(), it is called with the
//     argc/argv pair passed to main()

static int armci_init_called = 0;
static void **globalPtrs = NULL;

//
void chpl_comm_init(int *argc_p, char ***argv_p) {
  // This will probably be one of the trickiest routines to implement;
  // the details will depend on what sorts of mechanisms ARMCI
  // supports to create the multiple cooperating executables.  If, for
  // example, one needed to invoke an mpirun-like command to start the
  // program up, you'd want this routine to:
  //
  //   - for the user's invocation of the program, invoke that command
  //     on this same executable, adding an additional command line
  //     argument so that you could determine that those invocations
  //     were not the user's invocation
  //
  //   - for the non-user inovcations, you'd want to strip off those
  //     sentinel argv arguments so that Chapel's argument parsing
  //     routines wouldn't choke on them
  //
  // Don't forget to also set chpl_localeID and chpl_numLocales before
  // returning (this should only matter for the non-user invocations,
  // I believe)

  int nprocs, me;
  armci_size_t sz;

  MPI_SAFE(MPI_Init(argc_p, argv_p));
  ARMCI_SAFE(ARMCI_Init());
  armci_init_called = 1;

  MPI_SAFE(MPI_Comm_size(MPI_COMM_WORLD, &nprocs));
  MPI_SAFE(MPI_Comm_rank(MPI_COMM_WORLD, &me));

  chpl_localeID = me;
  chpl_numLocales = nprocs;

  globalPtrs = ARMCI_Malloc_local(chpl_numLocales * sizeof(void *));
  sz = _MAX_ARMCI_MEMSZ;

  ARMCI_SAFE(ARMCI_Malloc(globalPtrs, sz));

  ghndl = ARMCI_Gpc_register(gpc_call_handler);
}

int chpl_comm_run_in_gdb(int argc, char* argv[], int gdbArgnum, int* status) {
  chpl_error("--gdb not yet implemented for ARMCI", gdbArgnum, 
             "<command-line>");
  return 0;
}

void chpl_comm_init_shared_heap(void) {
  void* heapStart = chpl_numGlobalsOnHeap*sizeof(void*) + (char*)globalPtrs[chpl_localeID];
  size_t heapSize = _MAX_ARMCI_MEMSZ - chpl_numGlobalsOnHeap*sizeof(void*);
  initHeap(heapStart, heapSize);
}

//
// a final comm layer stub before barrier synching and calling into
// the user code.  It is recommended that a debugging message be
// printed here indicating that each locale has started using
// chpl_msg() and a verbosity level of 2 (which will cause it to be
// displayed using the -v flag).
//
void chpl_comm_rollcall(void) {
  // Something like the following should work:
  chpl_msg(2, "executing on locale %d of %d locale(s)\n", chpl_localeID, 
            chpl_numLocales);
}

void chpl_comm_alloc_registry(int numGlobals) {
  chpl_globals_registry = globalPtrs[chpl_localeID];
}

void chpl_comm_broadcast_global_vars(int numGlobals) {
  int i;

  if (chpl_localeID != 0) {
    for (i = 0; i < numGlobals; i++)
      chpl_comm_get(chpl_globals_registry[i], 0, &((void **)globalPtrs[0])[i], sizeof(void *), 0, "");
  }
}

typedef struct __broadcast_private_helper {
  void *addr;
  void *raddr;
  int locale;
  size_t size;
} _broadcast_private_helper;

static void _broadcastPrivateHelperFn(struct __broadcast_private_helper *arg);

void _broadcastPrivateHelperFn(struct __broadcast_private_helper *arg) {
  chpl_comm_get(arg->addr, arg->locale, arg->raddr, arg->size, 0, "");
}

void chpl_comm_broadcast_private(void* addr, int size) {
  int i;
  _broadcast_private_helper bph;
  void* heapAddr = NULL;

  heapAddr = chpl_malloc(1, size, "broadcast private", false, 0, 0);
  bcopy(addr, heapAddr, size);
  for (i = 0; i < chpl_numLocales; i++)
    if (i != chpl_localeID) {
      bph.addr = addr;
      bph.raddr = heapAddr;
      bph.locale = chpl_localeID;
      bph.size = size;

      // expected build error - this needs to be modified since fork
      // takes an fn id, not a function

      // This needs to be updated since chpl_comm_fork expects a fn id
      // instead of a function pointer
      chpl_comm_fork(i, _broadcastPrivateHelperFn, &bph, sizeof(_broadcast_private_helper));
    }
}

//
// barrier for synchronization between all processes; currently only
// used for startup and teardown.  msg is a string that can be used
// for debugging to determine where the barrier is being called.
//
void chpl_comm_barrier(const char *msg) {
  // Insert ARMCI barrier between all processes here
  ARMCI_Barrier();
}


static void chpl_comm_exit_common(int status)
{
  if (armci_init_called) {
    if (globalPtrs)
      ARMCI_Free_local(globalPtrs);

    if (ghndl != -1)
      ARMCI_Gpc_release(ghndl);

    ARMCI_Finalize();
    MPI_SAFE(MPI_Finalize());
  }
} /* chpl_comm_exit_common */

//
// terminates communication package at the end of a normal run of the
// chapel program -- assumes all processes are calling into the
// routine.  If the communication layer likes to call exit, the exit
// code is provided using the "status" argument; if it doesn't, it
// can simply return and the Chapel program will call exit().
//
// notes:
//   this function is called last
//   a barrier is invoked before calling into this function
//   Chapel's program termination is not yet implemented correctly
//
void chpl_comm_exit_all(int status) {
  // Insert cooperative ARMCI exit call here
  chpl_comm_exit_common(status);
}


//
// this routine should terminate the communication package when called
// by any thread, and should clean up the communication package's
// resources as best possible.  This routine is called whenever a user
// thread calls halt or exit and we have no guarantees that all threads
// are calling into the halt or exit.  Otherwise, it is much like the
// chpl_comm_exit_all() routine.
//
void chpl_comm_exit_any(int status) {
  // Insert "any one thread should be able to call" ARMCI exit call here
  chpl_comm_exit_common(status);
}


//
// write 'size' bytes of local data at 'addr' to remote data at
// 'raddr' on locale 'locale'
// notes:
//   address is arbitrary
//   size and locale are part of p
//
void  chpl_comm_put(void* addr, int32_t locale, void* raddr, int32_t size, int ln, char* fn) {
  // this should be an ARMCI put call

  if (chpl_localeID == locale)
    memmove(raddr, addr, size);
  else {
    chpl_mutex_lock(&armci_lock);
    ARMCI_SAFE(ARMCI_Put(addr, raddr, size, locale));
    chpl_mutex_unlock(&armci_lock);
  }
}


//
// read 'size' bytes of remote data at 'raddr' on locale 'locale' to
// local data at 'addr'
// notes:
//   address is arbitrary
//   size and locale are part of p
//
void  chpl_comm_get(void *addr, int32_t locale, void* raddr, int32_t size, int ln, char* fn) {
  // this should be an ARMCI get call

  if (chpl_localeID == locale)
    memmove(addr, raddr, size);
  else {
    chpl_mutex_lock(&armci_lock);
    ARMCI_SAFE(ARMCI_Get((void*)raddr, addr, size, locale));
    chpl_mutex_unlock(&armci_lock);
  }
}

//
// remote fork should launch a thread on locale that runs function f
// passing it arg where the size of arg is stored in arg_size
// notes:
//   multiple forks to the same locale should be handled concurrently
//

static void chpl_comm_fork_common(int locale, chpl_fn_int_t fid, void *arg, int arg_size, chpl_bool block) {
  const int rhdr_size = sizeof(int);

  int ret;
  void *header;
  volatile void *rheader;
  void *rdata;
  int rdlen;
  dist_fork_t *info;
  int info_size;
  volatile int *done;

  if (chpl_localeID == locale) {
    (*chpl_ftable[fid])(arg);
    return;
  }

  if (ghndl == -1) {
    chpl_internal_error("ARMCI GPC handler function not registered");
    return;
  }

  info_size = sizeof(dist_fork_t) + arg_size;
  info = (dist_fork_t *)chpl_malloc(info_size, sizeof(char), "chpl_comm_fork", false, __LINE__, __FILE__);

  info->caller = chpl_localeID;
  info->serial_state = chpl_get_serial();
  info->fid = fid;
  info->arg_size = arg_size;
  info->block = block;
  if (arg_size)
    bcopy(arg, &(info->arg), arg_size);

  if (arg_size > 0)
    rdata = chpl_malloc(arg_size, sizeof(char), "GPC exec remote data", false, __LINE__, __FILE__);
  else
    rdata = NULL;
  rdlen = arg_size;

  header = chpl_malloc(sizeof(void *), sizeof(char), "GPC exec remote header address",
                       false, __LINE__, __FILE__);
  rheader = chpl_malloc(rhdr_size, sizeof(char), "GPC exec remote header", false, __LINE__, __FILE__);
  // must be non-empty  

  *(intptr_t *)header = (intptr_t)rheader;

  done = rheader;
  *done = 0;

  chpl_mutex_lock(&armci_lock);
  ret = ARMCI_Gpc_exec(ghndl, locale, header, sizeof(void *), info, info_size, (void *)rheader, rhdr_size,
                       rdata, rdlen, NULL);
  chpl_mutex_unlock(&armci_lock);

  if (ret != 0) {
    chpl_internal_error("ARMCI_Gpc_exec() failed");
    chpl_free(info, __LINE__, __FILE__);
    if (rdata)
      chpl_free(rdata, __LINE__, __FILE__);
    chpl_free(header, __LINE__, __FILE__);
    chpl_free((void *)rheader, __LINE__, __FILE__);
    return;
  }

  while (block && *done == 0)
    ;

  chpl_free(info, __LINE__, __FILE__);
  if (rdata) {
    if (block)
      bcopy(rdata, arg, rdlen);
    chpl_free(rdata, __LINE__, __FILE__);
  }
  chpl_free(header, __LINE__, __FILE__);
  chpl_free((void *)rheader, __LINE__, __FILE__);
}

void  chpl_comm_fork(int locale, chpl_fn_int_t fid, void *arg, int arg_size) {
  chpl_comm_fork_common(locale, fid, arg, arg_size, true);
}

void  chpl_comm_fork_nb(int locale, chpl_fn_int_t fid, void *arg, int arg_size) {
  chpl_comm_fork_common(locale, fid, arg, arg_size, false);
}

void chpl_startVerboseComm() { }
void chpl_stopVerboseComm() { }
void chpl_startVerboseCommHere() { }
void chpl_stopVerboseCommHere() { }

void chpl_startCommDiagnostics() { }
void chpl_stopCommDiagnostics() { }
void chpl_startCommDiagnosticsHere() { }
void chpl_stopCommDiagnosticsHere() { }

int32_t chpl_numCommGets(void) { return -1; }
int32_t chpl_numCommPuts(void) { return -1; }
int32_t chpl_numCommForks(void) { return -1; }
int32_t chpl_numCommNBForks(void) { return -1; }

static void *_gpc_thread_handler(void *arg);

int gpc_call_handler(int to, int from, void *hdr, int hlen,
                     void *data,  int dlen,
                     void *rhdr,  int rhlen, int *rhsize,
                     void *rdata, int rdlen, int *rdsize,
                     int rtype)
{
  dist_fork_t *finfo;
  gpc_info_t *ginfo;
  intptr_t prhdr;

  finfo = chpl_malloc(dlen, sizeof(char), "Copy of input data", false, __LINE__, __FILE__);
  bcopy(data, finfo, dlen);

  ginfo = chpl_malloc(sizeof(gpc_info_t), sizeof(char), "fork struct", false, __LINE__, __FILE__);
  ginfo->info = finfo;
  prhdr = *(intptr_t *)hdr;
  ginfo->rhdr = (int *)prhdr;

  chpl_begin(_gpc_thread_handler, ginfo, true, finfo->serial_state, NULL);

  /* Small return header */
  *rhsize = sizeof(int);
  *rdsize = 0;

  return GPC_DONE;
} /* gpc_call_handler */

void *_gpc_thread_handler(void *arg)
{
  gpc_info_t *ginfo;
  int *done;

  done = ARMCI_Malloc_local(sizeof(int));

  *done = 0;
  ginfo = (gpc_info_t *)arg;

  if (ginfo->info->arg_size)
    (*chpl_ftable[ginfo->info->fid])(ginfo->info->arg);
  else
    (*chpl_ftable[ginfo->info->fid])(0);

  *done = 1;

  if (ginfo->info->block)
    chpl_comm_put(done, ginfo->info->caller, ginfo->rhdr, sizeof(int), 0, "");

  ARMCI_Free_local(done);

  chpl_free(ginfo->info, __LINE__, __FILE__);
  chpl_free(ginfo, __LINE__, __FILE__);

  return NULL;
} /* _gpc_thread_handler */
