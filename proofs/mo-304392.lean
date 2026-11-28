import OMAStatements.S_mo_304392
import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Counterexample to https://mathoverflow.net/questions/304392 in dimension three.
The six edges have shared marked points in their relative interiors. The
opposite hyperplanes are the three coordinate planes and the plane x+y+z=1.
Credit: @Spinausore, assisted by Codex (gpt-6.2-sol).
-/

open OMA.S_mo_304392
open scoped BigOperators

namespace Tetrahedron304392

private def metric : Fin 3 → Fin 3 → ℝ :=
  ![![135, -6, -390], ![-6, 36, -72], ![-390, -72, 1484]]

private noncomputable def t : Fin 4 → Fin 4 → ℝ :=
  ![![0, 3/4, 1/4, 1/2], ![1/4, 0, 1/2, 2/5],
    ![3/4, 1/2, 0, 2/3], ![1/2, 3/5, 1/3, 0]]

private def normal : Fin 4 → Fin 3 → ℝ :=
  ![![172, 153, 51], ![68, 177, 27], ![84, 1, 27], ![-752, -711, -237]]

private def offset : Fin 4 → ℝ := ![1206, 2412, 2412, -2412]

private theorem entry_two (a b c : ℝ) : (![a, b, c] : Fin 3 → ℝ) 2 = c := rfl

private theorem vertex3 (i : Fin 4) :
    vertex i = (![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![0, 0, 0]] : Fin 4 → Fin 3 → ℝ) i := by
  funext k
  fin_cases i <;> fin_cases k <;> rfl

private theorem pairing3 (x y : Fin 3 → ℝ) :
    pairing metric x y =
      x 0 * (135 * y 0 - 6 * y 1 - 390 * y 2) +
      x 1 * (-6 * y 0 + 36 * y 1 - 72 * y 2) +
      x 2 * (-390 * y 0 - 72 * y 1 + 1484 * y 2) := by
  simp [pairing, metric, Fin.sum_univ_succ]
  ring

private theorem positive (x : Fin 3 → ℝ) (hx : x ≠ 0) : 0 < pairing metric x x := by
  let a := x 0 - (2/45 : ℝ) * x 1 - (26/9 : ℝ) * x 2
  let b := x 1 - (5/2 : ℝ) * x 2
  have hsquares : pairing metric x x = 135 * a^2 + (536/15 : ℝ) * b^2 + 134 * (x 2)^2 := by
    rw [pairing3]
    dsimp [a, b]
    ring
  rw [hsquares]
  by_cases hz : x 2 = 0
  · by_cases hb : b = 0
    · have ha : a ≠ 0 := by
        intro ha
        have hy : x 1 = 0 := by simpa [b, hz] using hb
        have h0 : x 0 = 0 := by simpa [a, hy, hz] using ha
        apply hx
        funext k
        fin_cases k <;> assumption
      nlinarith [sq_pos_of_ne_zero ha, sq_nonneg b, sq_nonneg (x 2)]
    · nlinarith [sq_nonneg a, sq_pos_of_ne_zero hb, sq_nonneg (x 2)]
  · nlinarith [sq_nonneg a, sq_nonneg b, sq_pos_of_ne_zero hz]

private theorem symmetric (j k : Fin 3) : metric j k = metric k j := by
  fin_cases j <;> fin_cases k <;> rfl

private theorem edge (i j : Fin 4) (h : i ≠ j) :
    0 ≤ t i j ∧ t i j ≤ 1 ∧ t i j + t j i = 1 := by
  fin_cases i <;> fin_cases j <;> first | exact (h rfl).elim | norm_num [t]

private theorem normal_nonzero (i : Fin 4) : normal i ≠ 0 := by
  intro h
  have hz := congrFun h 0
  fin_cases i <;> norm_num [normal] at hz

private theorem through_edge (i j : Fin 4) (h : i ≠ j) :
    pairing metric (normal i) (segmentPoint i j (t i j)) = offset i := by
  fin_cases i <;> fin_cases j <;> first
    | exact (h rfl).elim
    | norm_num [pairing3, normal, segmentPoint, vertex3, t, offset, entry_two]

private theorem on_opposite (i : Fin 4) :
    faceCoordinate i (reflected metric (normal i) (offset i) (vertex i)) = 0 := by
  fin_cases i <;>
    norm_num [faceCoordinate, reflected, pairing3, normal, vertex3, offset, entry_two,
      Fin.sum_univ_succ]

theorem counterexample : ¬ (type_of% @OMA.S_mo_304392.main) := by
  intro h
  have bad := h 3 metric symmetric positive t normal offset
    edge normal_nonzero through_edge on_opposite 0 1 (by decide)
  norm_num [t] at bad

end Tetrahedron304392

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_304392.main) := Tetrahedron304392.counterexample
