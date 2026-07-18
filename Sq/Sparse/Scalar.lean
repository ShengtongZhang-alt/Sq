import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Scalar inequalities for the sparse square-energy argument

This file contains the graph-free real inequalities used in the induction for
the square-energy bound.  In particular, it does not depend on the graph or
matrix modules of this project.
-/

open scoped BigOperators

namespace SquareEnergy

/-- An oriented squared bound is equivalent to its square-root form when the
left side and the radicand are nonnegative. -/
lemma sq_le_mul_iff_le_sqrt_mul {S q T : ℝ} (hS : 0 ≤ S) (hprod : 0 ≤ q * T) :
    S ^ 2 ≤ q * T ↔ S ≤ √(q * T) :=
  (Real.le_sqrt hS hprod).symm

/-- The normalized square-energy bound is equivalent to the square-root bound
used when two inductive pieces are combined. -/
lemma four_mul_sq_le_iff_two_mul_le_sqrt_mul {S q T : ℝ}
    (hS : 0 ≤ S) (hprod : 0 ≤ q * T) :
    4 * S ^ 2 ≤ q * T ↔ 2 * S ≤ √(q * T) := by
  have htwoS : 0 ≤ 2 * S := by positivity
  rw [show 4 * S ^ 2 = (2 * S) ^ 2 by ring]
  exact (Real.le_sqrt htwoS hprod).symm

/-- Convert a normalized squared square-energy bound to its square-root form. -/
lemma two_mul_le_sqrt_mul_of_four_mul_sq_le {S q T : ℝ}
    (hS : 0 ≤ S) (hprod : 0 ≤ q * T) (h : 4 * S ^ 2 ≤ q * T) :
    2 * S ≤ √(q * T) :=
  (four_mul_sq_le_iff_two_mul_le_sqrt_mul hS hprod).mp h

/-- Convert a normalized square-root square-energy bound back to squared form. -/
lemma four_mul_sq_le_of_two_mul_le_sqrt_mul {S q T : ℝ}
    (hS : 0 ≤ S) (hprod : 0 ≤ q * T) (h : 2 * S ≤ √(q * T)) :
    4 * S ^ 2 ≤ q * T :=
  (four_mul_sq_le_iff_two_mul_le_sqrt_mul hS hprod).mpr h

/-- Finite-sum Cauchy--Schwarz in the form used for sums of inductive
square-root bounds. -/
lemma sum_sqrt_mul_le_sqrt_sum_mul_sum {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    (∑ i ∈ s, √(a i * b i)) ≤
      √((∑ i ∈ s, a i) * (∑ i ∈ s, b i)) := by
  calc
    (∑ i ∈ s, √(a i * b i)) =
        ∑ i ∈ s, √(a i) * √(b i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Real.sqrt_mul (ha i)]
    _ ≤ √(∑ i ∈ s, a i) * √(∑ i ∈ s, b i) :=
      Real.sum_sqrt_mul_sqrt_le s ha hb
    _ = √((∑ i ∈ s, a i) * (∑ i ∈ s, b i)) := by
      rw [Real.sqrt_mul (Finset.sum_nonneg fun i _ ↦ ha i)]

/-- The two-term scalar Cauchy--Schwarz inequality, written with one square
root around each product. -/
lemma sqrt_mul_add_sqrt_mul_le {q₁ q₂ T₁ T₂ : ℝ}
    (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂) (hT₁ : 0 ≤ T₁) (hT₂ : 0 ≤ T₂) :
    √(q₁ * T₁) + √(q₂ * T₂) ≤ √((q₁ + q₂) * (T₁ + T₂)) := by
  rw [Real.sqrt_mul hq₁, Real.sqrt_mul hq₂]
  apply Real.le_sqrt_of_sq_le
  nlinarith [Real.sq_sqrt hq₁, Real.sq_sqrt hq₂, Real.sq_sqrt hT₁,
    Real.sq_sqrt hT₂, sq_nonneg (√q₁ * √T₂ - √q₂ * √T₁)]

/-- Combine the normalized square-energy bounds for two nonnegative blocks. -/
lemma four_mul_sq_add_le_of_two_blocks {S₁ S₂ q₁ q₂ T₁ T₂ : ℝ}
    (hS₁ : 0 ≤ S₁) (hS₂ : 0 ≤ S₂)
    (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂) (hT₁ : 0 ≤ T₁) (hT₂ : 0 ≤ T₂)
    (h₁ : 4 * S₁ ^ 2 ≤ q₁ * T₁) (h₂ : 4 * S₂ ^ 2 ≤ q₂ * T₂) :
    4 * (S₁ + S₂) ^ 2 ≤ (q₁ + q₂) * (T₁ + T₂) := by
  have hroot₁ : 2 * S₁ ≤ √(q₁ * T₁) :=
    two_mul_le_sqrt_mul_of_four_mul_sq_le hS₁ (mul_nonneg hq₁ hT₁) h₁
  have hroot₂ : 2 * S₂ ≤ √(q₂ * T₂) :=
    two_mul_le_sqrt_mul_of_four_mul_sq_le hS₂ (mul_nonneg hq₂ hT₂) h₂
  apply (four_mul_sq_le_iff_two_mul_le_sqrt_mul
    (add_nonneg hS₁ hS₂) (mul_nonneg (add_nonneg hq₁ hq₂) (add_nonneg hT₁ hT₂))).mpr
  calc
    2 * (S₁ + S₂) = 2 * S₁ + 2 * S₂ := by ring
    _ ≤ √(q₁ * T₁) + √(q₂ * T₂) := add_le_add hroot₁ hroot₂
    _ ≤ √((q₁ + q₂) * (T₁ + T₂)) :=
      sqrt_mul_add_sqrt_mul_le hq₁ hq₂ hT₁ hT₂

/-- Cancel the common positive factor in the squared vertex-deletion estimate
and put the result into the paper's averaged form. -/
lemma averaged_estimate_of_scaled_bound {n q S T d₀ : ℝ} (hn : 2 < n)
    (hscaled :
      (2 * (n - 2) * S) ^ 2 ≤
        ((n - 2) * (q - 1)) * ((n - 2) * T + d₀)) :
    4 * S ^ 2 ≤ (q - 1) * T + (q - 1) / (n - 2) * d₀ := by
  have hn₂ : 0 < n - 2 := sub_pos.mpr hn
  have hfirst :
      (n - 2) * (4 * S ^ 2) ≤ (q - 1) * ((n - 2) * T + d₀) := by
    refine (mul_le_mul_iff_right₀ hn₂).mp ?_
    calc
      (n - 2) * ((n - 2) * (4 * S ^ 2)) =
          (2 * (n - 2) * S) ^ 2 := by ring
      _ ≤ ((n - 2) * (q - 1)) * ((n - 2) * T + d₀) := hscaled
      _ = (n - 2) * ((q - 1) * ((n - 2) * T + d₀)) := by ring
  have hcancel :
      (n - 2) * ((q - 1) / (n - 2)) = q - 1 := by
    calc
      (n - 2) * ((q - 1) / (n - 2)) =
          (q - 1) / (n - 2) * (n - 2) := by ring
      _ = q - 1 := div_mul_cancel₀ _ hn₂.ne'
  refine (mul_le_mul_iff_right₀ hn₂).mp ?_
  calc
    (n - 2) * (4 * S ^ 2) ≤ (q - 1) * ((n - 2) * T + d₀) := hfirst
    _ = (n - 2) * ((q - 1) * T) + (q - 1) * d₀ := by ring
    _ = (n - 2) * ((q - 1) * T) +
        ((n - 2) * ((q - 1) / (n - 2))) * d₀ := by
      rw [hcancel]
    _ = (n - 2) * ((q - 1) * T) +
        (n - 2) * ((q - 1) / (n - 2) * d₀) := by ring
    _ = (n - 2) * ((q - 1) * T + (q - 1) / (n - 2) * d₀) := by
      rw [mul_add]

/-- Derive the averaged estimate directly from the square-root inequality
obtained after summing the vertex-deletion induction hypotheses. -/
lemma averaged_estimate_of_sqrt_bound {n q S T d₀ : ℝ}
    (hn : 2 < n) (hq : 1 ≤ q) (hS : 0 ≤ S) (hT : 0 ≤ T) (hd₀ : 0 ≤ d₀)
    (hbound :
      2 * (n - 2) * S ≤
        √(((n - 2) * (q - 1)) * ((n - 2) * T + d₀))) :
    4 * S ^ 2 ≤ (q - 1) * T + (q - 1) / (n - 2) * d₀ := by
  have hn₂ : 0 < n - 2 := sub_pos.mpr hn
  have hq₁ : 0 ≤ q - 1 := sub_nonneg.mpr hq
  have htail : 0 ≤ (n - 2) * T + d₀ :=
    add_nonneg (mul_nonneg hn₂.le hT) hd₀
  have hradicand :
      0 ≤ ((n - 2) * (q - 1)) * ((n - 2) * T + d₀) :=
    mul_nonneg (mul_nonneg hn₂.le hq₁) htail
  have hleft : 0 ≤ 2 * (n - 2) * S := by positivity
  have hscaled :
      (2 * (n - 2) * S) ^ 2 ≤
        ((n - 2) * (q - 1)) * ((n - 2) * T + d₀) :=
    (Real.le_sqrt hleft hradicand).mp hbound
  exact averaged_estimate_of_scaled_bound hn hscaled

/-- Cauchy--Schwarz for a flat finite edge sum:
the square of a sum of square roots is at most the number of terms times
their sum. -/
lemma sq_sum_sqrt_le_card_mul_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) :
    (∑ i ∈ s, √(a i)) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, a i := by
  calc
    (∑ i ∈ s, √(a i)) ^ 2 ≤
        (s.card : ℝ) * ∑ i ∈ s, (√(a i)) ^ 2 :=
      sq_sum_le_card_mul_sum_sq (s := s) (f := fun i ↦ √(a i))
    _ = (s.card : ℝ) * ∑ i ∈ s, a i := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [Real.sq_sqrt (ha i hi)]

/-- The flat finite edge Cauchy--Schwarz estimate with the factor `4` used in
the square-energy theorem. -/
lemma four_mul_sq_sum_sqrt_le_card_mul_sum {ι : Type*}
    (s : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) :
    4 * (∑ i ∈ s, √(a i)) ^ 2 ≤
      4 * (s.card : ℝ) * ∑ i ∈ s, a i := by
  calc
    4 * (∑ i ∈ s, √(a i)) ^ 2 ≤
        4 * ((s.card : ℝ) * ∑ i ∈ s, a i) :=
      mul_le_mul_of_nonneg_left (sq_sum_sqrt_le_card_mul_sum s a ha) (by positivity)
    _ = 4 * (s.card : ℝ) * ∑ i ∈ s, a i := by ring

/-- Paper Case 1: the edge-count identity, flat estimate, and low-edge-mass
threshold imply the target square-energy bound. -/
lemma paper_case_one {m n q S d₀ w : ℝ}
    (hcount : 4 * m = 2 * q + 2 * (n - 1))
    (hflat : 4 * S ^ 2 ≤ 4 * m * w)
    (hthreshold : 2 * (n - 1) * w ≤ q * d₀) :
    4 * S ^ 2 ≤ q * (d₀ + 2 * w) := by
  calc
    4 * S ^ 2 ≤ 4 * m * w := hflat
    _ = 2 * q * w + 2 * (n - 1) * w := by rw [hcount]; ring
    _ ≤ 2 * q * w + q * d₀ := add_le_add le_rfl hthreshold
    _ = q * (d₀ + 2 * w) := by ring

/-- In Paper Case 2, simplicity bounds the coefficient of `d₀` after the
identity `q - 1 = (n - 2) + 2β` is substituted. -/
lemma paper_case_two_coefficient_le {n q β : ℝ}
    (hqβ : q - 1 = (n - 2) + 2 * β)
    (hsimple : 2 * β ≤ (n - 1) * (n - 2)) :
    2 * β * (n - 1) ≤ q * (n - 2) := by
  have hq : q = (n - 1) + 2 * β := by linarith
  have hgap : 0 ≤ (n - 1) * (n - 2) - 2 * β := sub_nonneg.mpr hsimple
  rw [hq]
  calc
    2 * β * (n - 1) ≤
        2 * β * (n - 1) + ((n - 1) * (n - 2) - 2 * β) :=
      le_add_of_nonneg_right hgap
    _ = ((n - 1) + 2 * β) * (n - 2) := by ring

/-- The strict Case 2 threshold gives the strict paper bound
`β d₀ < (n - 2) w`; all cancellations use an explicitly positive factor. -/
lemma paper_case_two_beta_mul_d_lt {n q β d₀ w : ℝ}
    (hn : 2 < n) (hd₀ : 0 ≤ d₀)
    (hqβ : q - 1 = (n - 2) + 2 * β)
    (hsimple : 2 * β ≤ (n - 1) * (n - 2))
    (hthreshold : q * d₀ < 2 * (n - 1) * w) :
    β * d₀ < (n - 2) * w := by
  have hn₂ : 0 < n - 2 := sub_pos.mpr hn
  have hn₁ : 0 < n - 1 := by linarith
  have hfactor : 0 < 2 * (n - 1) := mul_pos (by positivity) hn₁
  have hcoefficient :
      2 * β * (n - 1) ≤ q * (n - 2) :=
    paper_case_two_coefficient_le hqβ hsimple
  have hcoefficient_d :
      (2 * β * (n - 1)) * d₀ ≤ (q * (n - 2)) * d₀ :=
    mul_le_mul_of_nonneg_right hcoefficient hd₀
  have hthreshold_scaled :
      (q * d₀) * (n - 2) < (2 * (n - 1) * w) * (n - 2) :=
    mul_lt_mul_of_pos_right hthreshold hn₂
  have hscaled :
      (2 * (n - 1)) * (β * d₀) <
        (2 * (n - 1)) * ((n - 2) * w) := by
    calc
      (2 * (n - 1)) * (β * d₀) = (2 * β * (n - 1)) * d₀ := by ring
      _ ≤ (q * (n - 2)) * d₀ := hcoefficient_d
      _ = (q * d₀) * (n - 2) := by ring
      _ < (2 * (n - 1) * w) * (n - 2) := hthreshold_scaled
      _ = (2 * (n - 1)) * ((n - 2) * w) := by ring
  exact (mul_lt_mul_iff_right₀ hfactor).mp hscaled

/-- The weak Case 2 bound `β d₀ ≤ (n - 2) w` used by the averaged
correction estimate. -/
lemma paper_case_two_beta_mul_d_le {n q β d₀ w : ℝ}
    (hn : 2 < n) (hd₀ : 0 ≤ d₀)
    (hqβ : q - 1 = (n - 2) + 2 * β)
    (hsimple : 2 * β ≤ (n - 1) * (n - 2))
    (hthreshold : q * d₀ < 2 * (n - 1) * w) :
    β * d₀ ≤ (n - 2) * w :=
  (paper_case_two_beta_mul_d_lt hn hd₀ hqβ hsimple hthreshold).le

/-- The Case 2 beta bound controls the correction term in the averaged
estimate by `T = d₀ + 2w`. -/
lemma paper_case_two_averaged_correction_le {n q β d₀ w : ℝ}
    (hn : 2 < n) (hqβ : q - 1 = (n - 2) + 2 * β)
    (hβd : β * d₀ ≤ (n - 2) * w) :
    (q - 1) / (n - 2) * d₀ ≤ d₀ + 2 * w := by
  have hn₂ : 0 < n - 2 := sub_pos.mpr hn
  have htwice :
      2 * (β * d₀) ≤ 2 * ((n - 2) * w) :=
    mul_le_mul_of_nonneg_left hβd (by positivity)
  have hnumerator :
      (q - 1) * d₀ ≤ (d₀ + 2 * w) * (n - 2) := by
    calc
      (q - 1) * d₀ = ((n - 2) + 2 * β) * d₀ := by rw [hqβ]
      _ = (n - 2) * d₀ + 2 * (β * d₀) := by ring
      _ ≤ (n - 2) * d₀ + 2 * ((n - 2) * w) :=
        add_le_add le_rfl htwice
      _ = (d₀ + 2 * w) * (n - 2) := by ring
  calc
    (q - 1) / (n - 2) * d₀ = ((q - 1) * d₀) / (n - 2) := by ring
    _ ≤ d₀ + 2 * w := (div_le_iff₀ hn₂).mpr hnumerator

/-- Once the averaged correction is at most `T`, the averaged estimate is the
target bound `4S² ≤ qT`. -/
lemma paper_case_two_final_averaged_target {n q S T d₀ : ℝ}
    (haverage :
      4 * S ^ 2 ≤ (q - 1) * T + (q - 1) / (n - 2) * d₀)
    (hcorrection : (q - 1) / (n - 2) * d₀ ≤ T) :
    4 * S ^ 2 ≤ q * T := by
  calc
    4 * S ^ 2 ≤ (q - 1) * T + (q - 1) / (n - 2) * d₀ := haverage
    _ ≤ (q - 1) * T + T := add_le_add le_rfl hcorrection
    _ = q * T := by ring

/-- Paper Case 2 in assembled scalar form: simplicity and the high-edge-mass
threshold turn the averaged estimate into the target bound. -/
lemma paper_case_two {n q β S d₀ w : ℝ}
    (hn : 2 < n) (hd₀ : 0 ≤ d₀)
    (hqβ : q - 1 = (n - 2) + 2 * β)
    (hsimple : 2 * β ≤ (n - 1) * (n - 2))
    (hthreshold : q * d₀ < 2 * (n - 1) * w)
    (haverage :
      4 * S ^ 2 ≤
        (q - 1) * (d₀ + 2 * w) + (q - 1) / (n - 2) * d₀) :
    4 * S ^ 2 ≤ q * (d₀ + 2 * w) := by
  have hβd : β * d₀ ≤ (n - 2) * w :=
    paper_case_two_beta_mul_d_le hn hd₀ hqβ hsimple hthreshold
  have hcorrection :
      (q - 1) / (n - 2) * d₀ ≤ d₀ + 2 * w :=
    paper_case_two_averaged_correction_le hn hqβ hβd
  exact paper_case_two_final_averaged_target haverage hcorrection

/-- Cancel a positive `x` from `x² ≤ qx`; this is the final scalar step in
the spectral square-energy deduction. -/
lemma positive_cancel_sq_le_mul {x q : ℝ} (hx : 0 < x) (h : x ^ 2 ≤ q * x) :
    x ≤ q := by
  apply (mul_le_mul_iff_right₀ hx).mp
  calc
    x * x = x ^ 2 := by ring
    _ ≤ q * x := h
    _ = x * q := by ring

end SquareEnergy
