import data.int.basic
import tactic.linear_combination
import tactic.linarith

structure int_plane_non_zero :=
  (fst : ℤ) 
  (snd : ℤ) 
  (non_zero : snd ≠ 0)

def S (r s : int_plane_non_zero) : Prop :=
  r.1 * s.2 = s.1 * r.2

lemma S_def (r s : int_plane_non_zero) :
  S r s ↔ r.1 * s.2 = s.1 * r.2 := 
by refl

lemma S_refl : reflexive S :=
  λ r, by rw S_def

lemma S_symm : symmetric S :=
begin
  intros r s hrs,
  rw S_def at *,
  exact hrs.symm,
end

lemma S_trans : transitive S :=
begin
  intros r s t hrs hst,
  rw S_def at *,
  rw ← mul_right_inj' (s.non_zero),
  linear_combination t.snd * hrs + r.snd * hst,
end

lemma S_equiv : equivalence S :=
begin
  exact ⟨S_refl, S_symm, S_trans⟩,
end

instance s : setoid (int_plane_non_zero) :=
  { r     := S,
    iseqv := S_equiv }

notation `myrat` := quotient s

attribute [instance] s

namespace «myrat»

lemma equiv_def 
  (r s : int_plane_non_zero) 
  : r ≈ s ↔ r.1 * s.2 = s.1 * r.2 :=
begin
  refl
end

instance : has_zero myrat := 
  ⟨⟦(⟨0, 1, by norm_num⟩ : int_plane_non_zero)⟧⟩

instance : has_inv myrat :=
  { inv := quotient.lift (λ x : int_plane_non_zero, 
                          (if h : x.1 = 0 then (0 : myrat) 
                                          else ⟦⟨x.2, x.1, h⟩⟧ : myrat)) 
    begin
      rintros ⟨n, d, hd⟩ ⟨n', d', hd'⟩ (h : n*d' = n'*d),
      dsimp,
      split_ifs,
      { refl },
      { by finish },
    { by finish },
    { sorry },
    end }

end «myrat»
