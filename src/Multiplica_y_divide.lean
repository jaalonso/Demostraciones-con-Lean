import data.real.basic

variables {a b : ℝ} 

-- 1ª demostración
-- ===============

example 
  (h : b ≠ 0) 
  : a = b * (a / b) := 
(mul_div_cancel' _ h).symm

-- 2ª demostración
-- ===============

example : b ≠ 0 → a = b * (a / b) := 
begin
  intro h, 
  field_simp [h], 
  ring,
end
