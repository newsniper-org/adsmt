; Bake this with: lu-smt --aot-bake --aot-include-cdcl --aot-output p.luart-cdcl <this>
; Then: printf '(check-sat)\n' | lu-smt --aot-load p.luart-cdcl
; Expected: unsat (the (not true) is a flattenable contradiction).
; rc.27 AOT-load returns: sat  ← the (S.1) fix has not reached the AOT path.
(declare-const P Bool)
(declare-const Q Bool)
(declare-const R Bool)
(assert (=> P (and Q R)))
(assert (not true))
