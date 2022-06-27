-- Demostracion_sin_logica_clasica.lean
-- Demostración sin lógica clasica.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 27-junio-2022
-- ---------------------------------------------------------------------

import tactic

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar, sin usar lógica clásica, 
--    ¬(p ↔ ¬p)
-- ---------------------------------------------------------------------

variable p : Prop

-- 1ª demostración
example : ¬(p ↔ ¬p) :=
  ( assume hppf : p ↔ ¬p,
    have hppf1 : p → ¬p, from iff.elim_left hppf,
    have hppf2 : ¬p → p, from iff.elim_right hppf,
    have hpf : ¬p, from (assume hp : p, ((hppf1 hp) hp)),
    have hp : p, from (hppf2 hpf),
    (hppf1 hp) hp)

-- 2ª demostración
example : ¬(p ↔ ¬p) :=
begin
  by_contra h1,
  have hnp : ¬p , 
  { by_contra h2,
    have h3 : ¬ p := h1.mp h2,
    exact h3 h2, },
  apply hnp,
  exact h1.mpr hnp,
end
