from miasm.core.asmblock import disasmEngine
from miasm.arch.x86.arch import mn_x86


class dis_x86(disasmEngine):
    attrib = None

    def __init__(self, bs=None, **kwargs):
        super(dis_x86, self).__init__(mn_x86, self.attrib, bs, **kwargs)


class dis_x86_16(dis_x86):
    attrib = 16


class dis_x86_32(dis_x86):
    attrib = 32


class dis_x86_64(dis_x86):
    attrib = 64
