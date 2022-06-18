-- Cubo de una diferencia
-- ======================

import tactic

lemma expand_mult
  (a b : ℤ)
  : (b-a)^3 = b^3-3*a*b^2+3*a^2*b-a^3 :=
by ring_exp
