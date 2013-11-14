
//14656
struct pt_regs;
#if definedEx(CONFIG_LOCKDEP)

#if definedEx(CONFIG_X86_32)
//23360
struct pt_regs {unsigned long bx;};
#endif
#if !definedEx(CONFIG_X86_32)
//23412
struct pt_regs {unsigned long bx;};
#endif
//27374
struct kernel_vm86_regs {struct pt_regs pt;};
//42723
struct pt_regs;

//61688
struct pt_regs;

//76248
struct pt_regs;
#endif
#if !definedEx(CONFIG_LOCKDEP)

#if definedEx(CONFIG_X86_32)
//79401
struct pt_regs {unsigned long bx;};
#endif
#if !definedEx(CONFIG_X86_32)
//79453
struct pt_regs {unsigned long bx;};
#endif
//83415
struct kernel_vm86_regs {struct pt_regs pt;};
//98764
struct pt_regs;

//117729
struct pt_regs;
#endif

#if definedEx(CONFIG_X86_32)
//332800
struct pt_regs;
#endif

//335381
struct pt_regs;
