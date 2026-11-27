import OMAStatements.S_mo_335694
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Divisibility of the derivatives of a polynomial

Source: Seva, MathOverflow question 335694, July 8, 2019.
https://mathoverflow.net/questions/335694

Over any field of characteristic zero, the pairs in the original question
are precisely the translated, scaled powers with a low-degree perturbation.
For the allowed positive m, using natDegree also allows the zero remainder.
-/

namespace Proof335694
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

private theorem iter_degree (p : K[X]) (k : ℕ) :
    (derivative^[k] p).natDegree = p.natDegree - k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', natDegree_derivative, ih]
    omega

omit [CharZero K] in
private theorem quotient_degree {p f u r : K[X]} (h : p = u * f + r)
    (hf : f ≠ 0) (hr : r.natDegree < p.natDegree) :
    p.natDegree = u.natDegree + f.natDegree := by
  have hsub : p - r = u * f := by rw [h]; ring
  have hu : u ≠ 0 := by
    intro hu
    simp [hu] at h
    exact (Nat.ne_of_lt hr) (congrArg natDegree h.symm)
  calc
    p.natDegree = (p-r).natDegree := (natDegree_sub_eq_left_of_natDegree_lt hr).symm
    _ = _ := by rw [hsub, natDegree_mul hu hf]

private theorem euler_coeff (p : K[X]) (j : ℕ) :
    (X * derivative p).coeff j = (j : K) * p.coeff j := by
  cases j with
  | zero => simp
  | succ j => rw [coeff_X_mul, coeff_derivative, Nat.cast_succ, mul_comm]

/-- Translate to the root of the linear quotient. The Euler operator then
acts diagonally on every coefficient of degree at least m. -/
private theorem classify_linear {f t : K[X]} {u v w : K} {m : ℕ}
    (hu : u ≠ 0) (hm : 0 < m) (hd : m ≤ f.natDegree)
    (ht : t.natDegree < m)
    (h : (C u * X + C v) * derivative f = C w * f + t) :
    ∃ (a c : K) (r : K[X]), c ≠ 0 ∧ r.natDegree < m ∧
      f = C c * (X - C a) ^ f.natDegree + r := by
  let a : K := -v / u
  let g := f.comp (X + C a)
  let b := t.comp (X + C a)
  have hg : g.natDegree = f.natDegree := by simp [g, natDegree_comp]
  have hb : b.natDegree < m := by simpa [b, natDegree_comp] using ht
  have ha : u * a + v = 0 := by dsimp [a]; rw [mul_comm, div_mul_cancel₀ _ hu, neg_add_cancel]
  have hL : (C u * X + C v).comp (X + C a) = C u * X := by
    simp only [add_comp, mul_comp, C_comp, X_comp]
    rw [mul_add, ← map_mul, add_assoc, ← map_add, ha, map_zero, add_zero]
  have hD : (derivative f).comp (X + C a) = derivative g := by
    simp [g, derivative_comp]
  have he := congrArg (fun p : K[X] => p.comp (X + C a)) h
  change ((C u * X + C v) * derivative f).comp (X + C a) =
    (C w * f + t).comp (X + C a) at he
  rw [mul_comp, hL, hD, add_comp, mul_comp, C_comp, mul_assoc] at he
  have hcoeff (j : ℕ) (hj : m ≤ j) : (u * (j : K) - w) * g.coeff j = 0 := by
    have hj' := congrArg (fun p : K[X] => p.coeff j) he
    change (C u * (X * derivative g)).coeff j = (C w * g + b).coeff j at hj'
    rw [coeff_C_mul, euler_coeff, coeff_add, coeff_C_mul,
      coeff_eq_zero_of_natDegree_lt (hb.trans_le hj), add_zero] at hj'
    rw [sub_mul, mul_assoc, hj', sub_self]
  have hgn : g ≠ 0 := by intro h0; simp [h0] at hg; omega
  have hc : g.coeff f.natDegree ≠ 0 := by
    rw [← hg, coeff_natDegree]; exact leadingCoeff_ne_zero.mpr hgn
  have hw := (mul_eq_zero.mp (hcoeff f.natDegree hd)).resolve_right hc
  have hvan (j : ℕ) (hj : m ≤ j) (hne : j ≠ f.natDegree) : g.coeff j = 0 := by
    apply (mul_eq_zero.mp (hcoeff j hj)).resolve_left
    intro hz
    have hh := (sub_eq_zero.mp hz).trans (sub_eq_zero.mp hw).symm
    exact hne (Nat.cast_injective (mul_left_cancel₀ hu hh))
  let c := g.coeff f.natDegree
  let s := g - C c * X ^ f.natDegree
  have hs : s.natDegree < m := by
    suffices s.natDegree ≤ m - 1 by omega
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    simp only [s, coeff_sub, coeff_C_mul, coeff_X_pow]
    by_cases hje : j = f.natDegree
    · subst j; simp [c]
    · rw [if_neg hje, mul_zero, sub_zero]; exact hvan _ (by omega) hje
  refine ⟨a,c,s.comp (X - C a),hc,?_,?_⟩
  · simpa [natDegree_comp] using hs
  · have heq : g = C c * X ^ f.natDegree + s := by dsimp [s]; ring
    have hback := congrArg (fun p : K[X] => p.comp (X - C a)) heq
    simpa [g, comp_assoc, add_comp, mul_comp, pow_comp] using hback

private theorem necessity {f Q : K[X]} {m : ℕ} (hm : 0 < m)
    (hd : m ≤ f.natDegree) (hq : 0 < Q.natDegree)
    (h : ∀ k : ℕ, 1 ≤ k → k ≤ Q.natDegree → ∃ P R : K[X],
      (derivative^[k]) (Q * f) = P * f + R ∧ R.natDegree < m) :
    ∃ (a c : K) (r : K[X]), c ≠ 0 ∧ r.natDegree < m ∧
      f = C c * (X - C a) ^ f.natDegree + r := by
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  have hf : f ≠ 0 := by intro h0; simp [h0] at hd; omega
  have hQ : Q ≠ 0 := by intro h0; simp [h0] at hq
  obtain ⟨L,S,hL,hS⟩ : ∃ L S : K[X], (derivative^[j]) (Q*f) = L*f+S ∧ S.natDegree < m := by
    by_cases hj0 : j = 0
    · subst j; exact ⟨Q,0,by simp,by simpa using hm⟩
    · exact h j (by omega) (by omega)
  obtain ⟨D,T,hD,hT⟩ := h (j+1) (by omega) (by omega)
  have hprev : ((derivative^[j]) (Q*f)).natDegree = f.natDegree+1 := by
    rw [iter_degree, natDegree_mul hQ hf]; omega
  have hlast : ((derivative^[j+1]) (Q*f)).natDegree = f.natDegree := by
    rw [iter_degree, natDegree_mul hQ hf]; omega
  have hld := quotient_degree hL hf (by omega)
  have hdd := quotient_degree hD hf (by omega)
  have hl : L.natDegree = 1 := by omega
  have hd0 : D.natDegree = 0 := by omega
  have hu : L.coeff 1 ≠ 0 := by
    rw [← hl, coeff_natDegree, leadingCoeff_ne_zero]; intro h0; simp [h0] at hl
  have he := congrArg (derivative (R := K)) hL
  change derivative ((derivative^[j]) (Q*f)) = derivative (L*f+S) at he
  rw [← Function.iterate_succ_apply' (derivative (R := K)) j (Q*f), hD, map_add, derivative_mul] at he
  have hdl : derivative L = C (L.coeff 1) := by
    conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hl.le]
    simp [derivative_mul]
  rw [hdl, eq_C_of_natDegree_eq_zero hd0] at he
  apply classify_linear (u := L.coeff 1) (v := L.coeff 0) (w := D.coeff 0 - L.coeff 1)
    (t := T - derivative S) hu hm hd
  · have heS := natDegree_derivative_le S
    have hb := natDegree_sub_le T (derivative S)
    omega
  · rw [← eq_X_add_C_of_natDegree_le_one hl.le, map_sub, sub_mul]
    linear_combination -he

/-- Classification for the original range of degrees and all derivative orders. -/
theorem main (f : K[X]) (m : ℕ) (hm : 2 ≤ m) (hd : 2*m ≤ f.natDegree) :
    (∃ Q : K[X], 0 < Q.natDegree ∧ ∀ k : ℕ, 1 ≤ k → k ≤ Q.natDegree →
      ∃ P R : K[X], (derivative^[k]) (Q*f) = P*f+R ∧ R.natDegree < m) ↔
    ∃ (a c : K) (r : K[X]), c ≠ 0 ∧ r.natDegree < m ∧
      f = C c * (X - C a) ^ f.natDegree + r := by
  constructor
  · rintro ⟨Q,hQ,h⟩; exact necessity (by omega) (by omega) hQ h
  · rintro ⟨a,c,r,_,hr,hf⟩
    generalize hdg : f.natDegree = d at hf hd
    refine ⟨X - C a,by simp,?_⟩
    intro k hk hk'
    rw [natDegree_X_sub_C] at hk'
    have : k = 1 := by omega
    subst k
    let L : K[X] := X - C a
    refine ⟨C ((d:K)+1), L * derivative r - C (d:K) * r, ?_, ?_⟩
    · simp only [Function.iterate_one]
      rw [hf]
      have hder : derivative L = 1 := by simp [L]
      change derivative (L * (C c * L ^ d + r)) = _
      have hpow : L ^ (d-1) * L = L ^ d := by
        rw [← pow_succ]; congr 1; omega
      simp only [derivative_mul, map_add, derivative_C, zero_mul, zero_add,
        derivative_pow, hder, mul_one, one_mul, map_one]
      change _ = (C (d:K) + 1) * (C c * L^d + r) + (L * derivative r - C (d:K) * r)
      linear_combination (C c * C (d:K)) * hpow
    · have h1 : (L * derivative r).natDegree < m := by
        have hh := natDegree_mul_le (p := L) (q := derivative r)
        have hL : L.natDegree = 1 := natDegree_X_sub_C a
        have hh' := natDegree_derivative_le r
        omega
      have hh := natDegree_mul_le (p := C (d:K)) (q := r)
      rw [natDegree_C] at hh
      have hb := natDegree_sub_le (L * derivative r) (C (d:K) * r)
      omega

omit [CharZero K] in
/-- For a fixed upper bound N on the derivative order, the choice Q = f^N works. -/
theorem fixed_orders (f : K[X]) (N k : ℕ) (hk : k ≤ N) :
    f ∣ (derivative^[k]) (f^N * f) := by
  rw [← pow_succ]
  have hd := pow_sub_dvd_iterate_derivative_pow f (N+1) k
  have hstep := pow_dvd_pow f (show 1 ≤ N+1-k by omega)
  simpa using hstep.trans hd

omit [CharZero K] in
/-- For a quadratic g, Q = g^h has degree 2h. Taking f = g²
gives exact divisibility through order h. -/
theorem half_orders (g : K[X]) (h k : ℕ) (hk : k ≤ h) :
    g^2 ∣ (derivative^[k]) (g^h * g^2) := by
  rw [← pow_add]
  exact (pow_dvd_pow g (show 2 ≤ h+2-k by omega)).trans
    (pow_sub_dvd_iterate_derivative_pow g (h+2) k)

end Proof335694

theorem OMA.solution : type_of% @OMA.S_mo_335694.main := @Proof335694.main
