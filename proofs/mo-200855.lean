import OMAStatements.S_mo_200855
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# A twelve-vertex counterexample to MathOverflow 200855

Source: https://mathoverflow.net/questions/200855
Credit: @Spinausore

Take two copies of the complete graph on six vertices and match corresponding
vertices across the two copies. Let a=0, b=1 belong to the top clique, and let
c=6 be matched to a. Use t=1/14. The original graph is 6-regular, so each
centrality equals 7/4. Removing ab gives x_a=490/303 and adding bc gives
z_c=392/207. Thus x_a/y_a=280/303 < 207/224=y_c/z_c: the cross-products
are 62720 and 62721. This disproves the original strict inequality.

The integer vectors below are certificates for all twelve equations of each
linear system. Strict diagonal dominance gives uniqueness.
-/

namespace Counterexample200855
open OMA.S_mo_200855
open scoped BigOperators
open Matrix

private abbrev V := Fin 12
private abbrev Graph := V → V → Bool

private def prism (i j : V) : Bool :=
  decide (i ≠ j ∧ (i.val / 6 = j.val / 6 ∨ i.val % 6 = j.val % 6))

private abbrev cut : Graph := edit prism 0 1 false
private abbrev joined : Graph := edit prism 1 6 true

/-- For 12 vertices and t=1/14, every loopless Boolean adjacency matrix
gives a strictly diagonally dominant linear system. -/
private theorem invertibleSystem (G : Graph) (hdiag : ∀ i, G i i = false) :
    IsUnit (1 - (1/14 : ℝ) • realAdj G).det := by
  apply isUnit_iff_ne_zero.mpr
  apply det_ne_zero_of_sum_row_lt_diag
  intro i
  have hentry (j : V) (hj : j ∈ Finset.univ.erase i) :
      ‖(1 - (1/14 : ℝ) • realAdj G) i j‖ ≤ 1/14 := by
    have hne : i ≠ j := (Finset.ne_of_mem_erase hj).symm
    cases hv : G i j <;>
      norm_num [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, realAdj, hne, hv, Real.norm_eq_abs]
  calc
    _ ≤ ∑ _j ∈ Finset.univ.erase i, (1/14 : ℝ) := Finset.sum_le_sum hentry
    _ < _ := by
      norm_num [Finset.card_erase_of_mem, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.one_apply, realAdj, hdiag, Real.norm_eq_abs]

/-- An integer certificate for (I - G/14) w/den = 1:
14*w_i equals 14*den plus the sum of w over the neighbors of i. -/
private theorem scoreFromCertificate (G : Graph) (w : V → ℕ) (den : ℕ)
    (hden : 0 < den) (hdiag : ∀ i, G i i = false)
    (hrow : ∀ i, 14 * w i = 14 * den + ∑ j, if G i j then w j else 0) (i : V) :
    score G (1/14) i = (w i : ℝ) / den := by
  let v : V → ℝ := fun j => w j / (den : ℝ)
  let A := 1 - (1/14 : ℝ) • realAdj G
  have hn : (den : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hden)
  have hv : A.mulVec v = fun _ => 1 := by
    funext j
    have hw : (14:ℝ) * w j = 14 * den + ∑ k, if G j k then (w k : ℝ) else 0 := by
      exact_mod_cast hrow j
    have hs : (realAdj G).mulVec v j =
        (∑ k, if G j k then (w k : ℝ) else 0) / den := by
      rw [div_eq_mul_inv, Finset.sum_mul]
      change (∑ k : V, realAdj G j k * v k) = _
      apply Finset.sum_congr rfl
      intro k _
      cases he : G j k <;> simp [realAdj, v, he, div_eq_mul_inv]
    change ((1 - (1/14 : ℝ) • realAdj G).mulVec v) j = 1
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, hs]
    change (w j : ℝ) / den - 1/14 * ((∑ k, if G j k then (w k : ℝ) else 0) / den) = 1
    field_simp
    linarith
  change (A⁻¹.mulVec (fun _ => 1)) i = v i
  rw [← hv, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A (invertibleSystem G hdiag), Matrix.one_mulVec]

private def cutWeights (i : V) : ℕ :=
  if i.val < 2 then 7840 else if i.val < 6 then 8365 else if i.val < 8 then 8428 else 8463

private def joinedWeights (i : V) : ℕ :=
  if i = 1 ∨ i = 6 then 1568 else if i = 0 ∨ i = 7 then 1470 else 1463

private theorem originalScore (i : V) : score prism (1/14) i = 7/4 := by
  exact scoreFromCertificate prism (fun _ => 7) 4 (by decide) (by decide) (by decide) i

private theorem cutScore : score cut (1/14) 0 = 490/303 := by
  rw [scoreFromCertificate cut cutWeights 4848 (by decide) (by decide) (by decide)]
  norm_num [cutWeights]

private theorem joinedScore : score joined (1/14) 6 = 392/207 := by
  rw [scoreFromCertificate joined joinedWeights 828 (by decide) (by decide) (by decide)]
  norm_num [joinedWeights]

end Counterexample200855

open Counterexample200855 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_200855.main) := by
  intro h
  have bad := h 12 (by decide) prism 0 1 6 (1/14) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by norm_num) (by norm_num) (by rw [originalScore, originalScore])
      (by rw [originalScore, originalScore])
  change OMA.S_mo_200855.score Counterexample200855.cut _ 0 / _ >
    _ / OMA.S_mo_200855.score Counterexample200855.joined _ 6 at bad
  rw [Counterexample200855.cutScore, Counterexample200855.joinedScore,
    Counterexample200855.originalScore, Counterexample200855.originalScore] at bad
  norm_num at bad
