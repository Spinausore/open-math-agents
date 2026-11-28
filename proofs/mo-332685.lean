import OMAStatements.S_mo_332685
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Tactic.NormNum

-- Source: https://mathoverflow.net/questions/332685
-- Credit: @Spinausore

open Polynomial OMA.S_mo_332685

namespace Sharpness332685

noncomputable def E : Biv ℚ := X - C X
noncomputable def P : Biv ℚ := C X * (X - 1)

private theorem outerE : E.natDegree = 1 := by
  simp [E]

private theorem innerE : degreeX E = 1 := by
  have hs : swap E = C (X : Polynomial ℚ) - X := by
    simp [swap, E]
  rw [degreeX, hs]
  have hn : C (X : Polynomial ℚ) - (X : Biv ℚ) = -(X - C (X : Polynomial ℚ)) :=
    (neg_sub _ _).symm
  rw [hn, natDegree_neg, natDegree_X_sub_C]

private theorem outerP : P.natDegree = 1 := by
  rw [P, natDegree_mul (C_ne_zero.mpr X_ne_zero) (by simpa using X_sub_C_ne_zero (1 : Polynomial ℚ))]
  have h := natDegree_X_sub_C (1 : Polynomial ℚ)
  simpa using h

private theorem innerP : degreeX P = 1 := by
  have hc : C (X - 1 : Polynomial ℚ) = C X - (1 : Biv ℚ) := by
    rw [map_sub, map_one]
  have hs : swap P = (X : Biv ℚ) * C (X - 1) := by
    rw [hc]
    simp [P, swap]
  rw [degreeX, hs, natDegree_mul X_ne_zero (C_ne_zero.mpr (by simpa using X_sub_C_ne_zero (1 : ℚ)))]
  simp only [natDegree_X, natDegree_C, Nat.add_zero]

private theorem specializeX (i : Fin 2) : atX (i.val : ℚ) E ∣ atX (i.val : ℚ) P := by
  have hi : i.val = 0 ∨ i.val = 1 := by omega
  rcases hi with h | h
  · simp [atX, E, P, h]
  · simp [atX, E, P, h]

private theorem specializeY (i : Fin 2) : atY (i.val : ℚ) E ∣ atY (i.val : ℚ) P := by
  have hi : i.val = 0 ∨ i.val = 1 := by omega
  rcases hi with h | h
  · simp [atY, E, P, h]
  · simp [atY, E, P, h]

private theorem not_dvd : ¬ E ∣ P := by
  rintro ⟨Q, hQ⟩
  let ev : Biv ℚ →+* ℚ := (evalRingHom 2).comp (evalRingHom (C (2 : ℚ)))
  have h := congrArg ev hQ
  have he : ev E = 0 := by norm_num [ev, E]
  have hp : ev P = 2 := by norm_num [ev, P]
  rw [map_mul, he, zero_mul, hp] at h
  norm_num at h

theorem result : type_of% @OMA.S_mo_332685.main := by
  let points : Fin 2 → ℚ := fun i => i.val
  have hi : Function.Injective points := by
    intro i j h
    change (i.val : ℚ) = (j.val : ℚ) at h
    exact Fin.ext (by exact_mod_cast h)
  refine ⟨ℚ, inferInstance, 2, 2, points, points, E, P, by decide, by decide, hi, hi,
    ?_, ?_, ?_, ?_, ?_, specializeX, specializeY, not_dvd⟩
  · intro h
    have hdeg := outerE
    simp [h] at hdeg
  · intro h
    have hdeg := outerP
    simp [h] at hdeg
  · rw [innerE, innerP]
  · rw [outerE, outerP]
  · rw [innerP, outerP]

end Sharpness332685

theorem OMA.solution : type_of% @OMA.S_mo_332685.main := Sharpness332685.result
