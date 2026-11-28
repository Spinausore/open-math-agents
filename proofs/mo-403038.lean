import OMAStatements.S_mo_403038
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# An explicit polynomial with ten distinct real roots

Credit: @Spinausore. Source: https://mathoverflow.net/questions/403038

The example is -1/34000 times the product of x² - s*x - 1 for
s in {2,4,9,11,-26}. Each factor has two simple real roots. A root x
determines s uniquely from s*x = x²-1, since x is nonzero.
-/

namespace TenRealRoots
open OMA.S_mo_403038

private def q (s x : ℝ) := x^2 - s*x - 1

private def slope : Fin 5 → ℤ
  | 0 => 2
  | 1 => 4
  | 2 => 9
  | 3 => 11
  | 4 => -26

private noncomputable def root (s : ℝ) (b : Bool) : ℝ :=
  if b then (s + Real.sqrt (s^2+4))/2 else (s - Real.sqrt (s^2+4))/2

private theorem quadratic (s x : ℝ) :
    q s x = (x-root s false)*(x-root s true) := by
  have hs : 0 ≤ s^2+4 := by positivity
  simp only [q,root, Bool.false_eq_true, if_false, if_true]
  nlinarith [Real.sq_sqrt hs]

private theorem q_zero (s x : ℝ) : q s x = 0 ↔ ∃ b, root s b = x := by
  rw [quadratic, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact ⟨false, (sub_eq_zero.mp h).symm⟩
    · exact ⟨true, (sub_eq_zero.mp h).symm⟩
  · rintro ⟨b, rfl⟩
    cases b <;> simp

private theorem pair_injective (s : ℝ) : Function.Injective (root s) := by
  have hs : 0 < Real.sqrt (s^2+4) := Real.sqrt_pos.2 (by positivity)
  intro b c h
  cases b <;> cases c <;> try rfl
  all_goals
    exfalso
    simp only [root, Bool.false_eq_true, if_true, if_false] at h
    linarith

private noncomputable def value (i : Fin 5 × Bool) := root (slope i.1) i.2

private theorem value_injective : Function.Injective value := by
  rintro ⟨i,b⟩ ⟨j,c⟩ h
  let x := root (slope i) b
  change x = root (slope j) c at h
  have hi := (q_zero (slope i) x).2 ⟨b,rfl⟩
  have hj := (q_zero (slope j) x).2 ⟨c,h.symm⟩
  have hx : x ≠ 0 := by intro h0; rw [h0] at hi; norm_num [q] at hi
  have hz : ((slope i : ℝ) - slope j) * x = 0 := by
    dsimp [q] at hi hj
    nlinarith
  have hs : slope i = slope j := by
    exact_mod_cast (sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hx))
  have hslope : Function.Injective slope := by decide
  have hij := hslope hs
  subst j
  exact Prod.ext rfl (pair_injective _ h)

private noncomputable def exampleP : ℝ → ℝ :=
  family (-1/34000) (455/34000) (-5148/34000) (17000/34000)
    (-5148/34000) (-34455/34000) (1/34000)

private theorem factors (x : ℝ) : exampleP x =
    (-1 / 34000) * q 2 x * q 4 x * q 9 x * q 11 x * q (-26) x := by
  unfold exampleP family q
  ring

private theorem factor_zeros (x : ℝ) : exampleP x = 0 ↔ ∃ i : Fin 5, q (slope i) x = 0 := by
  rw [factors]
  simp only [mul_eq_zero]
  constructor
  · rintro (((((h | h) | h) | h) | h) | h)
    · norm_num at h
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
    · exact ⟨2,h⟩
    · exact ⟨3,h⟩
    · exact ⟨4,by simpa [slope] using h⟩
  · rintro ⟨i,h⟩
    fin_cases i <;> simp_all [slope]

end TenRealRoots

open TenRealRoots in
theorem OMA.solution : type_of% @OMA.S_mo_403038.main := by
  classical
  let index : Fin 10 ≃ (Fin 5 × Bool) := Fintype.equivOfCardEq (by simp)
  refine ⟨-1/34000,455/34000,-5148/34000,17000/34000,-5148/34000,-34455/34000,1/34000,
    by norm_num,by norm_num,value ∘ index,value_injective.comp index.injective,?_⟩
  intro x
  change exampleP x = 0 ↔ ∃ j, value (index j) = x
  rw [factor_zeros]
  constructor
  · rintro ⟨i,hi⟩
    obtain ⟨b,hb⟩ := (q_zero _ _).1 hi
    exact ⟨index.symm (i,b), by simpa [value] using hb⟩
  · rintro ⟨j,hj⟩
    exact ⟨(index j).1,(q_zero _ _).2 ⟨(index j).2,hj⟩⟩
