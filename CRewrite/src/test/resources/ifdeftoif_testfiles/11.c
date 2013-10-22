struct mm_struct;
typedef unsigned long long u64;

typedef u64 phys_addr_t;
typedef u64	pgprotval_t;
typedef struct pgprot { pgprotval_t pgprot; } pgprot_t;

typedef u64	pteval_t;
typedef u64	pmdval_t;
typedef u64	pudval_t;
typedef u64	pgdval_t;
typedef u64	pgprotval_t;
typedef union {
	struct {
		unsigned long pte_low, pte_high;
	};
	pteval_t pte;
} pte_t;

typedef struct { pudval_t pud; } pud_t;
typedef struct { pud_t pud; } pmd_t;

typedef struct { pgdval_t pgd; } pgd_t;

struct paravirt_callee_save {
	void *func;
};
struct pv_lazy_ops {
	/* Set deferred update mode, used for batching operations. */
	void (*enter)(void);
	void (*leave)(void);
};
#if (definedEx(CONFIG_B))
struct pv_mmu_ops {
#endif
#if (!definedEx(CONFIG_B))
struct pv_mmu_ops {
#endif

#if (definedEx(CONFIG_A))
	void (*set_pmd_at)(struct mm_struct *mm, unsigned long addr,
			   pmd_t *pmdp, pmd_t pmdval);
#endif
#if (!definedEx(CONFIG_A))
	void (*set_pmd_at)(struct mm_struct *mm, unsigned long addr,
			   pmd_t *pmdp, pmd_t pmdval);
#endif

};

extern struct pv_mmu_ops pv_mmu_ops;
