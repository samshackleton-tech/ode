"""Run an AArch64 function on this CPU (Linux, aarch64).

The bytes are written to a temporary file and mapped read+execute
(the kernel makes freshly mapped executable pages coherent with the
instruction cache), then called through ctypes with the in/out/scratch
buffers the checker proved the code stays within.
"""
import ctypes
import os
import tempfile

_libc = ctypes.CDLL(None, use_errno=True)
_libc.mmap.restype = ctypes.c_void_p
_libc.mmap.argtypes = [ctypes.c_void_p, ctypes.c_size_t, ctypes.c_int,
                       ctypes.c_int, ctypes.c_int, ctypes.c_long]
PROT_READ, PROT_EXEC, MAP_PRIVATE = 1, 4, 2
_SIG = ctypes.CFUNCTYPE(None, ctypes.c_void_p, ctypes.c_void_p, ctypes.c_void_p)


class Function:
    def __init__(self, code, n_in, n_out, scratch):
        fd, path = tempfile.mkstemp()
        try:
            os.write(fd, code)
            addr = _libc.mmap(None, len(code), PROT_READ | PROT_EXEC,
                              MAP_PRIVATE, fd, 0)
        finally:
            os.close(fd)
            os.unlink(path)
        if addr in (None, ctypes.c_void_p(-1).value):
            raise OSError(ctypes.get_errno(), "mmap failed")
        self.fn = _SIG(addr)
        self.inp = (ctypes.c_uint32 * max(1, n_in))()
        self.out = (ctypes.c_uint32 * max(1, n_out))()
        self.scr = (ctypes.c_uint32 * max(1, scratch))()
        self.n_in, self.n_out = n_in, n_out

    def __call__(self, values):
        assert len(values) == self.n_in
        for i, v in enumerate(values):
            self.inp[i] = v
        self.fn(ctypes.addressof(self.inp), ctypes.addressof(self.out),
                ctypes.addressof(self.scr))
        return list(self.out[:self.n_out])
