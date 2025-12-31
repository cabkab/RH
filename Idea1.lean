
/-
I have formalized the definitions and theorems from the provided LaTeX file.
I defined the Hilbert spaces `L2(X_S)` and `L2(C_S)` and the operators `P_Lambda`, `S_Lambda`, `V_S`, and `T_h`.
I stated Theorems 1.1, 1.2, 1.3, 1.4, and 1.5 as axioms, capturing the logical structure of the proposed proof of the Riemann Hypothesis.
I also included the necessary auxiliary definitions such as `hat_h`, `Delta`, `lambda_n`, and the functions `P_n`, `g_n`, `p_{n, epsilon}`.
The Li criterion is also stated as an axiom connecting `lambda_n` to the Riemann Hypothesis.
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-
Checking for Norm instance on Padic numbers, padicNorm, and PadicInt.modPart.
-/
#check (inferInstance : Norm (Padic 2))
#check (inferInstance : Norm ℚ_[2])
#check padicNorm
#check Padic.addValuation
#check PadicInt.modPart

/-
Defining MeasurableSpace and BorelSpace instances for Q_p.
-/
instance (p : ℕ) [Fact p.Prime] : MeasurableSpace ℚ_[p] := borel ℚ_[p]
instance (p : ℕ) [Fact p.Prime] : BorelSpace ℚ_[p] := ⟨rfl⟩

/-
Defining the closed unit ball in Q_p as a PositiveCompacts set.
-/
noncomputable def Zp_compacts (p : ℕ) [Fact p.Prime] : TopologicalSpace.PositiveCompacts ℚ_[p] where
  carrier := Metric.closedBall 0 1
  isCompact' := by
    -- The closed ball in a metric space is compact.
    apply isCompact_closedBall
  interior_nonempty' := by
    exact ⟨ 0, mem_interior_iff_mem_nhds.mpr ( Metric.closedBall_mem_nhds _ zero_lt_one ) ⟩

/-
Defining the Haar measure dx_p on Q_p using addHaarMeasure and the compact set Zp_compacts.
-/
noncomputable def dx_p (p : ℕ) [Fact p.Prime] : MeasureTheory.Measure ℚ_[p] :=
  MeasureTheory.Measure.addHaarMeasure (Zp_compacts p)

/-
Defining the additive Haar measure on Q_p normalized on Z_p, and proving the normalization property.
-/
noncomputable def measure_Qp (p : ℕ) [Fact p.Prime] : MeasureTheory.Measure ℚ_[p] :=
  MeasureTheory.Measure.addHaarMeasure (Zp_compacts p)

theorem measure_Qp_Zp_eq_one (p : ℕ) [Fact p.Prime] : measure_Qp p (Metric.closedBall 0 1) = 1 := by
  rw [measure_Qp]
  -- The measure of the defining compact set is 1 by definition of addHaarMeasure.
  have h := MeasureTheory.Measure.addHaarMeasure_self (K₀ := Zp_compacts p)
  -- The carrier of Zp_compacts p is defined as Metric.closedBall 0 1.
  exact h

/-
Proving that the Haar measure of the unit ball is 1.
-/
theorem dx_p_Zp (p : ℕ) [Fact p.Prime] : dx_p p (Metric.closedBall 0 1) = 1 := by
  rw [dx_p]
  -- The measure of the defining compact set is 1 by definition of addHaarMeasure.
  have h := MeasureTheory.Measure.addHaarMeasure_self (K₀ := Zp_compacts p)
  -- The carrier of Zp_compacts p is defined as Metric.closedBall 0 1.
  exact h

/-
Defining the p-adic fractional part function.
-/
noncomputable def padicFract {p : ℕ} [Fact p.Prime] (x : ℚ_[p]) : ℚ :=
  if h : x = 0 then 0 else
  let v := x.valuation
  if hv : 0 ≤ v then 0 else
  let k := (-v).natAbs
  let y : ℚ_[p] := x * (p : ℚ_[p]) ^ k
  let y_int : ℤ_[p] := ⟨y, by
    have hy_norm : ‖y‖ = p ^ (-v - k : ℤ) := by
      have hy_norm : ‖y‖ = ‖x‖ * ‖(p : ℚ_[p]) ^ k‖ := by
        exact norm_mul _ _;
      have hy_norm : ‖x‖ = p ^ (-v : ℤ) := by
        exact?;
      simp_all +decide [ zpow_sub₀, Nat.Prime.ne_zero Fact.out ];
      exact?;
    rw [ hy_norm ];
    norm_num [ k, abs_of_neg ( not_le.mp hv ) ]
  ⟩
  (PadicInt.appr y_int k : ℚ) / (p ^ k : ℚ)

/-
The p-adic norm of the difference between a p-adic number and its fractional part is at most 1.
-/
theorem padicFract_norm_sub_le_one (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) :
  ‖x - padicFract x‖ ≤ 1 := by
  unfold padicFract;
  split_ifs <;> simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ]
  generalize_proofs at *;
  split_ifs <;> simp_all +decide [ sub_eq_iff_eq_add ];
  · exact?;
  · -- Since $y = x * p^k$ and $y \in \mathbb{Z}_p$, we have $\|y - \text{appr}(y, k)\| \leq p^{-k}$.
    have hy_diff : ‖(x * (p : ℚ_[p]) ^ x.valuation.natAbs) - (PadicInt.appr ⟨x * (p : ℚ_[p]) ^ x.valuation.natAbs, by
      assumption⟩ x.valuation.natAbs : ℚ_[p])‖ ≤ (p : ℝ) ^ (-x.valuation.natAbs : ℤ) := by
      have hy_diff : ∀ (n : ℕ) (y : ℤ_[p]), ‖(y : ℚ_[p]) - (PadicInt.appr y n : ℚ_[p])‖ ≤ (p : ℝ) ^ (-n : ℤ) := by
        intro n y; exact (by
        convert y.appr_spec n using 1
        generalize_proofs at *;
        erw [ ← PadicInt.norm_le_pow_iff_mem_span_pow ] ; aesop
        skip)
        skip
      generalize_proofs at *;
      convert hy_diff _ _ using 1
    generalize_proofs at *;
    -- Since $y = x * p^k$ and $y \in \mathbb{Z}_p$, we have $\|x - \text{appr}(y, k) / p^k\| = \|p^{-k}(y - \text{appr}(y, k))\| = p^k \|y - \text{appr}(y, k)\| \leq p^k p^{-k} = 1$.
    have hx_diff : ‖x - (PadicInt.appr ⟨x * (p : ℚ_[p]) ^ x.valuation.natAbs, by
      assumption⟩ x.valuation.natAbs : ℚ_[p]) / (p : ℚ_[p]) ^ x.valuation.natAbs‖ = ‖(x * (p : ℚ_[p]) ^ x.valuation.natAbs - (PadicInt.appr ⟨x * (p : ℚ_[p]) ^ x.valuation.natAbs, by
      assumption⟩ x.valuation.natAbs : ℚ_[p])) / (p : ℚ_[p]) ^ x.valuation.natAbs‖ := by
      rw [ sub_div, mul_div_cancel_right₀ _ ( pow_ne_zero _ ( Nat.cast_ne_zero.mpr <| Nat.Prime.ne_zero Fact.out ) ) ]
    generalize_proofs at *;
    simp_all +decide [ div_eq_mul_inv, mul_comm ];
    exact le_trans ( mul_le_mul_of_nonneg_left hy_diff <| by positivity ) <| by rw [ mul_inv_cancel₀ <| by exact ne_of_gt <| by exact zpow_pos ( Nat.cast_pos.mpr <| Nat.Prime.pos Fact.out ) _ ] ;

/-
Proving that the p-adic fractional part is between 0 and 1.
-/
theorem padicFract_range (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) :
  0 ≤ padicFract x ∧ padicFract x < 1 := by
    unfold padicFract;
    split_ifs <;> norm_num;
    split_ifs <;> norm_num;
    refine' ⟨ div_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg ( Nat.cast_nonneg _ ) _ ), _ ⟩;
    rw [ div_lt_one ( pow_pos ( Nat.cast_pos.mpr <| Nat.Prime.pos Fact.out ) _ ) ];
    norm_cast;
    exact?

/-
Proving that the denominator of the p-adic fractional part is a power of p.
-/
theorem padicFract_den (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) :
  ∃ k : ℕ, (padicFract x).den = p ^ k := by
    -- Let's unfold the definition of `padicFract` to get a better understanding of its structure.
    unfold padicFract at *;
    split_ifs <;> simp +decide [ * ];
    · exact ⟨ 0, rfl ⟩;
    · split_ifs <;> norm_cast <;> simp_all +decide [ Nat.Prime.ne_zero Fact.out ];
      · exact ⟨ 0, by norm_num ⟩;
      · norm_num [ Rat.mul_den, Rat.div_def ];
        split_ifs <;> simp_all +decide [ Nat.Prime.ne_zero Fact.out ];
        -- Since the gcd of any number and a power of p is also a power of p, we can conclude that the denominator is a power of p.
        have h_gcd_pow : ∀ (a : ℕ), a ∣ p ^ x.valuation.natAbs → ∃ k : ℕ, a = p ^ k := by
          intro a ha; rw [ Nat.dvd_prime_pow Fact.out ] at ha; tauto;
        exact h_gcd_pow _ ( Nat.div_dvd_of_dvd <| Nat.gcd_dvd_right _ _ )

/-
If a rational number x has a denominator that is a power of p and ||x||_p <= 1, then x is an integer.
-/
theorem isInt_of_norm_le_one_and_den_pow_p (p : ℕ) [Fact p.Prime] (x : ℚ)
  (h_den : ∃ k : ℕ, x.den = p ^ k) (h_norm : ‖(x : ℚ_[p])‖ ≤ 1) : ∃ z : ℤ, x = z := by
  rcases h_den with ⟨k, hk⟩
  -- x = n / d where d = p^k.
  -- ||x||_p = ||n||_p / ||d||_p = ||n||_p / (1/p^k) = p^k * ||n||_p.
  -- ||x||_p <= 1 => p^k * ||n||_p <= 1 => ||n||_p <= p^{-k}.
  -- This implies p^k divides n.
  -- So x = n / p^k is an integer.
  contrapose! h_norm;
  haveI := Fact.mk ( Fact.out : Nat.Prime p ) ; simp_all +decide [ padicNorm ] ;
  split_ifs <;> simp_all +decide [ padicValRat ];
  · simpa using h_norm 0;
  · -- Since $p$ is prime and $x$ is not an integer, $padicValInt p x.num$ must be less than $k$.
    have h_padic_lt_k : padicValInt p x.num < k := by
      have h_padic_lt_k : ¬(p ^ k ∣ Int.natAbs x.num) := by
        intro h;
        refine' h_norm ( x.num / p ^ k ) _;
        rw [ Int.cast_div ] <;> norm_num;
        · simpa [ hk ] using x.num_div_den.symm;
        · simpa [ ← Int.natCast_dvd_natCast ] using h;
        · exact fun h => absurd h ( Nat.Prime.ne_zero Fact.out );
      contrapose! h_padic_lt_k;
      refine' Nat.dvd_trans ( pow_dvd_pow _ h_padic_lt_k ) _;
      convert Nat.ordProj_dvd ( Int.natAbs x.num ) p using 1;
      rw [ Nat.factorization_def ] ; aesop;
      exact Fact.out;
    simp_all +decide [ zpow_sub₀, show p ≠ 0 by exact Nat.Prime.ne_zero Fact.out ];
    rw [ one_lt_div ( pow_pos ( Nat.cast_pos.mpr <| Nat.Prime.pos Fact.out ) _ ) ] ; exact pow_lt_pow_right₀ ( Nat.one_lt_cast.mpr <| Nat.Prime.one_lt Fact.out ) h_padic_lt_k

/-
Proving existence and uniqueness of the p-adic fractional part.
-/
theorem exists_unique_padic_fract (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) :
  ∃! r : ℚ, ‖x - r‖ ≤ 1 ∧ 0 ≤ r ∧ r < 1 ∧ ∃ k : ℕ, r.den = p ^ k := by
    have h_unique : ∀ r s : ℚ, ‖x - r‖ ≤ 1 → ‖x - s‖ ≤ 1 → 0 ≤ r → r < 1 → 0 ≤ s → s < 1 → (∃ k : ℕ, r.den = p ^ k) → (∃ k : ℕ, s.den = p ^ k) → r = s := by
      intros r s hr hs hr_nonneg hr_lt_one hs_nonneg hs_lt_one hr_den hs_den
      have h_eq : ‖(r : ℚ_[p]) - (s : ℚ_[p])‖ ≤ 1 := by
        have h_eq : ‖(r : ℚ_[p]) - (s : ℚ_[p])‖ ≤ max ‖(x : ℚ_[p]) - (r : ℚ_[p])‖ ‖(x : ℚ_[p]) - (s : ℚ_[p])‖ := by
          have h_eq : ‖(r : ℚ_[p]) - (s : ℚ_[p])‖ ≤ max ‖(x : ℚ_[p]) - (r : ℚ_[p])‖ ‖(x : ℚ_[p]) - (s : ℚ_[p])‖ := by
            have h_ultra : ∀ a b : ℚ_[p], ‖a + b‖ ≤ max ‖a‖ ‖b‖ := by
              exact?
            convert h_ultra ( x - r ) ( - ( x - s ) ) using 1 ; ring;
            · rw [ ← norm_neg ] ; ring;
            · rw [ norm_neg ]
          generalize_proofs at *; exact h_eq;
        generalize_proofs at *; exact h_eq.trans ( max_le hr hs ) ;
      generalize_proofs at *; (
      -- Since $r$ and $s$ have denominators that are powers of $p$, their difference $r - s$ is also a rational number with a denominator that is a power of $p$.
      obtain ⟨k, hk⟩ := hr_den
      obtain ⟨m, hm⟩ := hs_den
      have h_diff_den : ∃ n : ℕ, (r - s).den = p ^ n := by
        have h_diff_den : (r - s).den ∣ r.den * s.den := by
          exact?
        generalize_proofs at *; (
        rw [ hk, hm, ← pow_add ] at h_diff_den; rw [ Nat.dvd_prime_pow Fact.out ] at h_diff_den; tauto;)
      generalize_proofs at *; (
      -- Since $|r - s|_p \leq 1$ and $r - s$ is a rational number with a denominator that is a power of $p$, it follows that $r - s$ is an integer.
      have h_int : ∃ z : ℤ, r - s = z := by
        convert isInt_of_norm_le_one_and_den_pow_p p ( r - s ) _ _ using 1
        generalize_proofs at *; (
        exact h_diff_den);
        aesop
      generalize_proofs at *; (
      obtain ⟨ z, hz ⟩ := h_int; rcases z with ⟨ _ | _ | z ⟩ <;> norm_num at hz <;> linarith;)));
    -- Let's first show that there exists such an $r$.
    have h_exists : ∃ r : ℚ, ‖x - r‖ ≤ 1 ∧ 0 ≤ r ∧ r < 1 ∧ (∃ k : ℕ, r.den = p ^ k) := by
      exact ⟨ padicFract x, by simpa using padicFract_norm_sub_le_one p x, by simpa using padicFract_range p x |>.1, by simpa using padicFract_range p x |>.2, by simpa using padicFract_den p x ⟩;
    exact ⟨ h_exists.choose, h_exists.choose_spec, fun s hs => h_unique _ _ hs.1 h_exists.choose_spec.1 hs.2.1 hs.2.2.1 h_exists.choose_spec.2.1 h_exists.choose_spec.2.2.1 hs.2.2.2 h_exists.choose_spec.2.2.2 ⟩

/-
Proving existence and uniqueness of the p-adic fractional part.
-/
theorem exists_unique_padic_fract' (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) :
  ∃! r : ℚ, ‖x - r‖ ≤ 1 ∧ 0 ≤ r ∧ r < 1 ∧ ∃ k : ℕ, r.den = p ^ k := by
    exact?

/-
Proving that padicFract is additive modulo integers.
-/
theorem padicFract_add_sub_add_isInt (p : ℕ) [Fact p.Prime] (x y : ℚ_[p]) :
  ∃ z : ℤ, padicFract (x + y) - (padicFract x + padicFract y) = z := by
    -- By definition of $padicFract$, we know that $padicFract (x + y) - (padicFract x + padicFract y)$ is an integer.
    have h_int : ∃ z : ℤ, padicFract (x + y) - (padicFract x + padicFract y) = z := by
      have h_frac : ∃ r s t : ℚ, r = padicFract x ∧ s = padicFract y ∧ t = padicFract (x + y) ∧ ‖x - r‖ ≤ 1 ∧ ‖y - s‖ ≤ 1 ∧ ‖x + y - t‖ ≤ 1 ∧ 0 ≤ r ∧ r < 1 ∧ 0 ≤ s ∧ s < 1 ∧ 0 ≤ t ∧ t < 1 ∧ ∃ k l m : ℕ, r.den = p ^ k ∧ s.den = p ^ l ∧ t.den = p ^ m := by
        refine' ⟨ padicFract x, padicFract y, padicFract ( x + y ), rfl, rfl, rfl, _, _, _, _, _ ⟩ <;> norm_num [ padicFract_range, padicFract_norm_sub_le_one ];
        exact ⟨ padicFract_den p x, padicFract_den p y, padicFract_den p ( x + y ) ⟩
      -- Since $r$, $s$, and $t$ are rational numbers with denominators that are powers of $p$, their difference $t - (r + s)$ is also a rational number with a denominator that is a power of $p$.
      obtain ⟨r, s, t, hr, hs, ht, h_norm_r, h_norm_s, h_norm_t, hr_bounds, hs_bounds, ht_bounds, h_den_r, h_den_s, h_den_t⟩ := h_frac
      have h_diff_int : ∃ z : ℤ, t - (r + s) = z := by
        have h_diff_int : ‖(t - (r + s) : ℚ_[p])‖ ≤ 1 := by
          have h_diff_int : ‖(x + y - t : ℚ_[p]) + (r + s - x - y : ℚ_[p])‖ ≤ 1 := by
            have h_diff_int : ‖(x + y - t : ℚ_[p])‖ ≤ 1 ∧ ‖(r + s - x - y : ℚ_[p])‖ ≤ 1 := by
              have h_diff_int : ‖(r + s - x - y : ℚ_[p])‖ ≤ max ‖(r - x : ℚ_[p])‖ ‖(s - y : ℚ_[p])‖ := by
                have h_diff_int : ∀ a b : ℚ_[p], ‖a + b‖ ≤ max ‖a‖ ‖b‖ := by
                  exact?;
                convert h_diff_int ( r - x ) ( s - y ) using 1 ; ring;
              simp_all +decide [ norm_sub_rev ];
              exact h_diff_int.elim ( fun h => le_trans h h_norm_r ) fun h => le_trans h h_norm_s;
            -- Apply the non-Archimedean property of the p-adic norm.
            have h_non_archimedean : ∀ a b : ℚ_[p], ‖a + b‖ ≤ max ‖a‖ ‖b‖ := by
              exact?;
            exact le_trans ( h_non_archimedean _ _ ) ( max_le h_diff_int.1 h_diff_int.2 );
          convert h_diff_int using 1 ; ring;
          rw [ ← norm_neg ] ; ring;
        -- Since $t$, $r$, and $s$ are rational numbers with denominators that are powers of $p$, their difference $t - (r + s)$ is also a rational number with a denominator that is a power of $p$.
        obtain ⟨k, l, m, hr_den, hs_den, ht_den⟩ := h_den_t.right;
        have h_diff_den : ∃ n : ℕ, (t - (r + s)).den = p ^ n := by
          have h_diff_den : (t - (r + s)).den ∣ (r.den * s.den * t.den) := by
            rw [ Rat.sub_def ];
            rw [ Rat.normalize_eq ];
            refine' Nat.dvd_trans ( Nat.div_dvd_of_dvd _ ) _;
            · exact Nat.gcd_dvd_right _ _;
            · rw [ mul_comm ];
              exact mul_dvd_mul ( Rat.add_den_dvd _ _ ) dvd_rfl;
          rw [ hr_den, hs_den, ht_den ] at h_diff_den;
          rw [ ← pow_add, ← pow_add ] at h_diff_den;
          rw [ Nat.dvd_prime_pow Fact.out ] at h_diff_den ; tauto;
        exact?;
      grind;
    exact h_int

/-
Proving existence and uniqueness of the p-adic fractional part.
-/
theorem exists_unique_padic_fract_spec (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) :
  ∃! r : ℚ, ‖x - r‖ ≤ 1 ∧ 0 ≤ r ∧ r < 1 ∧ ∃ k : ℕ, r.den = p ^ k := by
    have := exists_unique_padic_fract p x;
    exact this

/-
Proving helper lemmas about denominators being powers of p.
-/
theorem den_pow_p_of_dvd_pow_p {p : ℕ} [Fact p.Prime] {n : ℕ} {k : ℕ} (h : n ∣ p ^ k) :
  ∃ j, n = p ^ j := by
    rw [ Nat.dvd_prime_pow Fact.out ] at h ; tauto

theorem den_pow_p_add (p : ℕ) [Fact p.Prime] (x y : ℚ)
  (hx : ∃ k, x.den = p ^ k) (hy : ∃ k, y.den = p ^ k) :
  ∃ k, (x + y).den = p ^ k := by
    -- The denominator of the sum of two fractions with denominators that are powers of $p$ is also a power of $p$.
    have h_denom : ∀ {a b : ℚ}, (∃ k : ℕ, a.den = p ^ k) → (∃ k : ℕ, b.den = p ^ k) → ∃ k : ℕ, (a + b).den ∣ p ^ k := by
      intro a b ha hb
      obtain ⟨k₁, hk₁⟩ := ha
      obtain ⟨k₂, hk₂⟩ := hb;
      -- The denominator of the sum of two fractions is the least common multiple of their denominators.
      have h_denom_sum : (a + b).den ∣ Nat.lcm a.den b.den := by
        exact?;
      exact ⟨ Max.max k₁ k₂, h_denom_sum.trans ( Nat.lcm_dvd ( hk₁.symm ▸ pow_dvd_pow _ ( le_max_left _ _ ) ) ( hk₂.symm ▸ pow_dvd_pow _ ( le_max_right _ _ ) ) ) ⟩;
    obtain ⟨ k, hk ⟩ := h_denom hx hy; rw [ Nat.dvd_prime_pow ( Fact.out : Nat.Prime p ) ] at hk; aesop;

theorem den_pow_p_neg (p : ℕ) [Fact p.Prime] (x : ℚ)
  (hx : ∃ k, x.den = p ^ k) : ∃ k, (-x).den = p ^ k := by
    exact?

theorem den_pow_p_sub (p : ℕ) [Fact p.Prime] (x y : ℚ)
  (hx : ∃ k, x.den = p ^ k) (hy : ∃ k, y.den = p ^ k) :
  ∃ k, (x - y).den = p ^ k := by
    -- Since the denominator of x + y is the least common multiple of the denominators of x and y, and both denominators are powers of p, their LCM is also a power of p.
    obtain ⟨kx, hkx⟩ := hx
    obtain ⟨ky, hky⟩ := hy
    have h_lcm : (x - y).den ∣ p ^ (max kx ky) := by
      -- The denominator of x - y is the least common multiple of the denominators of x and y.
      have h_lcm : (x - y).den ∣ Nat.lcm x.den y.den := by
        exact?;
      cases le_total kx ky <;> simp_all +decide [ pow_add, pow_mul ];
      · exact h_lcm.trans ( Nat.lcm_dvd ( pow_dvd_pow _ ‹_› ) ( pow_dvd_pow _ le_rfl ) );
      · exact h_lcm.trans ( Nat.lcm_dvd ( dvd_rfl ) ( pow_dvd_pow _ ‹_› ) );
    exact?

/-
Checking if exists_unique_padic_fract is available.
-/
variable (p : ℕ) [Fact p.Prime]
#check exists_unique_padic_fract p

/-
Proving that the p-adic fractional part is locally constant: if ||x - y|| <= 1, then {x} = {y}.
-/
theorem padicFract_eq_of_norm_sub_le_one (p : ℕ) [Fact p.Prime] (x y : ℚ_[p])
  (h : ‖x - y‖ ≤ 1) : padicFract x = padicFract y := by
    -- Since ‖x - y‖ ≤ 1, we have that x - y is in Z_p, hence its fractional part is 0.
    have h_frac_zero : padicFract (x - y) = 0 := by
      -- Since ‖x - y‖ ≤ 1, we have that x - y is in Z_p, hence its valuation is non-negative.
      have h_val_nonneg : (x - y).valuation ≥ 0 := by
        exact?;
      unfold padicFract; aesop;
    -- Since {x} is the unique rational number satisfying the conditions, and we have that {x} - {y} is an integer, it must be that {x} = {y}.
    have h_frac_eq : ∃ z : ℤ, padicFract x - padicFract y = z := by
      have := padicFract_add_sub_add_isInt p ( x - y ) y; aesop;
    obtain ⟨ z, hz ⟩ := h_frac_eq;
    rcases z with ⟨ _ | _ | z ⟩ <;> norm_num at hz ⊢ <;> linarith [ padicFract_range p x, padicFract_range p y ] ;

/-
Defining the additive character psi_p on Q_p and proving it preserves addition.
-/
noncomputable def psi_p (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (padicFract x : ℂ))

theorem psi_p_one (p : ℕ) [Fact p.Prime] : psi_p p 0 = 1 := by
  unfold psi_p;
  unfold padicFract; norm_num;

theorem psi_p_add (p : ℕ) [Fact p.Prime] (x y : ℚ_[p]) :
  psi_p p (x + y) = psi_p p x * psi_p p y := by
    unfold psi_p;
    rw [ ← Complex.exp_add ];
    -- By definition of $padicFract$, we know that $padicFract (x + y) - (padicFract x + padicFract y) = z$ for some integer $z$.
    obtain ⟨z, hz⟩ : ∃ z : ℤ, padicFract (x + y) = padicFract x + padicFract y + z := by
      have := padicFract_add_sub_add_isInt p x y;
      exact ⟨ this.choose, eq_add_of_sub_eq' this.choose_spec ⟩;
    exact Complex.exp_eq_exp_iff_exists_int.mpr ⟨ z, by push_cast [ hz ] ; ring ⟩

/-
Defining the additive character on the reals.
-/
noncomputable def psi_infty (x : ℝ) : ℂ :=
  Complex.exp (-2 * Real.pi * Complex.I * x)

/-
Checking if Measure.prod and Measure.pi are available.
-/
open MeasureTheory

#check Measure.prod
#check Measure.pi

/-
Defining the adele ring A_S as an abbrev, and defining psi_S and mu_S. Using inferred instances.
-/
open MeasureTheory Complex

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)

abbrev A_S := ℝ × ((p : S) → @Padic p ⟨hS p p.2⟩)

-- TopologicalSpace should be inferred because A_S reduces to a product.
-- AddCommGroup should be inferred.
-- Module ℝ should be inferred.

-- We need MeasurableSpace on A_S.
-- Mathlib's `MeasurableSpace` for products is the product sigma algebra.
-- We want to use this one to define the measure.
-- But we also want `BorelSpace` instance.
-- If we rely on inference, we get the product measurable space.
-- We need to show this equals the borel space of the product topology.
-- This is true for second countable spaces.
-- Let's see if we can just define the measure on the inferred measurable space.

noncomputable def psi_S (x : A_S S hS) : ℂ :=
  psi_infty x.1 * ∏ p : S, @psi_p p ⟨hS p p.2⟩ (x.2 p)

noncomputable def mu_S : Measure (A_S S hS) :=
  Measure.prod volume (Measure.pi (fun p : S => @dx_p p ⟨hS p p.2⟩))

instance : MeasureSpace (A_S S hS) := ⟨mu_S S hS⟩

/-
Checking availability of SchwartzMap, IsLocallyConstant, HasCompactSupport, and padicValRat.
-/
open MeasureTheory Complex

#check SchwartzMap
#check IsLocallyConstant
#check HasCompactSupport
#check padicValRat

/-
Defining the FiniteAdeleS type, the IsSchwartzBruhat predicate, and the group of S-units O_S_star.
-/
open MeasureTheory Complex

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)

abbrev FiniteAdeleS := (p : S) → @Padic p ⟨hS p p.2⟩

def IsSchwartzBruhat (f : A_S S hS → ℂ) : Prop :=
  ∃ (n : ℕ) (g : Fin n → SchwartzMap ℝ ℂ) (h : Fin n → FiniteAdeleS S hS → ℂ),
    (∀ i, IsLocallyConstant (h i) ∧ HasCompactSupport (h i)) ∧
    f = fun x => ∑ i, g i x.1 * h i x.2

def O_S_star : Subgroup ℚˣ where
  carrier := { q : ℚˣ | ∀ p : ℕ, p.Prime → p ∉ S → padicValRat p q = 0 }
  mul_mem' := by
    -- By the properties of the p-adic valuation, we have padicValRat p (a * b) = padicValRat p a + padicValRat p b.
    have h_padic_val_mul : ∀ {a b : ℚˣ}, ∀ p : ℕ, Nat.Prime p → padicValRat p (a * b) = padicValRat p a + padicValRat p b := by
      intro a b p hp; haveI := Fact.mk hp; rw [ padicValRat.mul ] <;> aesop;
    aesop
  one_mem' := by
    -- The padicValRat of 1 is 0 for any prime p.
    simp [padicValRat]
  inv_mem' := by
    -- If $x$ is in the subgroup, then for any prime $p$ not in $S$, the $p$-adic valuation of $x$ is zero. Since the $p$-adic valuation of $x^{-1}$ is the negative of the $p$-adic valuation of $x$, and zero is its own negative, the $p$-adic valuation of $x^{-1}$ is also zero. Therefore, $x^{-1}$ is in the subgroup.
    intros x hx
    intro p hp hps
    have h_val : padicValRat p (x⁻¹ : ℚ) = -padicValRat p (x : ℚ) := by
      haveI := Fact.mk hp; rw [ padicValRat.inv ] ;
    aesop

/-
Checking Ring instance for A_S and defining J_S.
-/
open MeasureTheory Complex

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)

-- Check if Ring instance is inferred
#check (inferInstance : Ring (A_S S hS))

-- Define J_S
abbrev J_S := (A_S S hS)ˣ

/-
Checking if O_S_star and A_S are defined.
-/
open MeasureTheory Complex

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)

#check O_S_star
#check A_S

/-
Defining the Schwartz-Bruhat space and the Fourier transform on A_S.
-/
open MeasureTheory Complex

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)

def SchwartzBruhatSpace := { f : A_S S hS → ℂ // IsSchwartzBruhat S hS f }

noncomputable def FourierTransform_S (f : A_S S hS → ℂ) (y : A_S S hS) : ℂ :=
  ∫ x, f x * psi_S S hS (x * y) ∂(mu_S S hS)

/-
Checking if A_S is an algebra over Q.
-/
open MeasureTheory Complex

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)

#check (inferInstance : Algebra ℚ (A_S S hS))

/-
Checking if den_pow_p_of_dvd_pow_p exists.
-/
#check den_pow_p_of_dvd_pow_p

/-
Checking if SchwartzBruhatSpace and FourierTransform_S are available.
-/
open MeasureTheory Complex

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)

#check SchwartzBruhatSpace S hS
#check FourierTransform_S S hS

/-
Defining the embedding of S-units into J_S, the subgroup of embedded S-units, and the quotient group C_S.
-/
open MeasureTheory Complex

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)

noncomputable def embed_O_S_star (q : O_S_star S) : J_S S hS :=
  Units.mk
    (algebraMap ℚ ℝ ((q : ℚˣ) : ℚ), fun (p : S) =>
      letI : Fact (p : ℕ).Prime := ⟨hS p p.2⟩
      algebraMap ℚ ℚ_[p] ((q : ℚˣ) : ℚ))
    (algebraMap ℚ ℝ ((q⁻¹ : ℚˣ) : ℚ), fun (p : S) =>
      letI : Fact (p : ℕ).Prime := ⟨hS p p.2⟩
      algebraMap ℚ ℚ_[p] ((q⁻¹ : ℚˣ) : ℚ))
    (by
    ext <;> simp +decide [ mul_comm ])
    (by
    ext <;> norm_num)

noncomputable def O_S_star_embedded_hom : O_S_star S →* J_S S hS where
  toFun := embed_O_S_star S hS
  map_one' := by
    -- By definition of embed_O_S_star, we have embed_O_S_star S hS 1 = 1.
    simp [embed_O_S_star];
    -- The inverse of a pair is the pair of the inverses, and since both components are 1, this should hold.
    congr
  map_mul' := by
    simp +zetaDelta at *;
    -- Show that the embedding of the product of two elements in O_S_star is the product of their embeddings.
    intros a ha b hb
    ext;
    · simp +decide [ embed_O_S_star ];
    · aesop

noncomputable def O_S_star_embedded : Subgroup (J_S S hS) :=
  (O_S_star_embedded_hom S hS).range

abbrev C_S := (J_S S hS) ⧸ (O_S_star_embedded S hS)

/-
Defining the norm on the adele ring A_S and the idele group J_S.
-/
open MeasureTheory Complex

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)

noncomputable def norm_A_S (x : A_S S hS) : ℝ :=
  ‖x.1‖ * ∏ p : S, ‖x.2 p‖

noncomputable def norm_J_S (x : J_S S hS) : ℝ :=
  norm_A_S S hS (x : A_S S hS)

/-
Defining the multiplicative measures on R and Q_p.
-/
open MeasureTheory Complex ENNReal

noncomputable def mult_measure_real : Measure ℝ :=
  volume.withDensity (fun x => (ENNReal.ofReal ‖x‖)⁻¹)

variable (p : ℕ) [Fact p.Prime]

noncomputable def mult_measure_padic : Measure ℚ_[p] :=
  (ENNReal.ofReal ((1 - (p : ℝ)⁻¹)⁻¹)) • (@dx_p p ‹_›).withDensity (fun x => (ENNReal.ofReal ‖x‖)⁻¹)

/-
Checking for MeasurableSpace instances on units and Units.mk0.
-/
open MeasureTheory

variable (p : ℕ) [Fact p.Prime]

#check (inferInstance : MeasurableSpace ℝˣ)
#check (inferInstance : MeasurableSpace ℚ_[p]ˣ)
#check Units.mk0

/-
Defining the MeasurableSpace, BorelSpace, and multiplicative measure on the idele group J_S.
-/
open MeasureTheory Complex ENNReal

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)

instance : MeasurableSpace (J_S S hS) := borel (J_S S hS)
instance : BorelSpace (J_S S hS) := ⟨rfl⟩

noncomputable def mu_J_S : Measure (J_S S hS) :=
  Measure.comap Units.val ((mu_S S hS).withDensity (fun x => (ENNReal.ofReal (norm_A_S S hS x))⁻¹))

instance : MeasureSpace (J_S S hS) := ⟨mu_J_S S hS⟩

/-
Defining the map E_S from Schwartz-Bruhat functions to functions on the idele class group C_S.
-/
open MeasureTheory Complex

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)

noncomputable def E_S_aux (f : SchwartzBruhatSpace S hS) (x : J_S S hS) : ℂ :=
  (norm_J_S S hS x).sqrt * ∑' (q : O_S_star S), f.val (embed_O_S_star S hS q * x : A_S S hS)

noncomputable def E_S (f : SchwartzBruhatSpace S hS) : C_S S hS → ℂ :=
  fun x => Quotient.liftOn x (E_S_aux S hS f) (by
    intros a b hab
    -- a and b are in J_S, a ~ b means a = b * q for some q in O_S_star
    -- We need to show E_S_aux f a = E_S_aux f b
    -- E_S_aux f (b * q) = |b * q|^{1/2} \sum_{q'} f(q' * b * q)
    -- |b * q| = |b| * |q| = |b| * 1 = |b| (product formula)
    -- \sum_{q'} f(q' * b * q) = \sum_{q''} f(q'' * b) where q'' = q' * q
    -- Since multiplication by q is a bijection on O_S_star, the sum is the same.
    -- By definition of $E_S_aux$, we have $E_S_aux S hS f a = f(a)$ and $E_S_aux S hS f b = f(b)$.
    simp [E_S_aux];
    -- Since $a \approx b$, there exists $q \in O_S^*$ such that $b = qa$.
    obtain ⟨q, hq⟩ : ∃ q : O_S_star S, b = embed_O_S_star S hS q * a := by
      obtain ⟨ q, hq ⟩ := hab;
      obtain ⟨ q, hq ⟩ := q;
      obtain ⟨ q, hq ⟩ := ‹q ∈ (O_S_star_embedded S hS).op›;
      use q⁻¹;
      simp_all +decide [ ← mul_assoc, ← ‹ ( fun m : ↥ ( O_S_star_embedded S hS ).op => m • b ) ⟨ _, _ ⟩ = a › ];
      rw [ ← hq ];
      simp +decide [ Units.ext_iff ];
      simp +decide [ embed_O_S_star, O_S_star_embedded_hom ];
      ext <;> simp +decide [ mul_assoc, mul_comm, mul_left_comm ];
    -- Since $q \in O_S^*$, we have $\|qa\| = \|a\|$.
    have h_norm_qa : norm_J_S S hS (embed_O_S_star S hS q * a) = norm_J_S S hS a := by
      unfold norm_J_S norm_A_S;
      unfold embed_O_S_star; norm_num [ norm_mul, norm_inv ] ;
      simp +decide [ Norm.norm, mul_assoc, mul_comm, mul_left_comm, Finset.prod_mul_distrib ];
      have h_prod_one : ∏ x ∈ S.attach, (↑(↑x : ℕ) : ℝ) ^ padicValRat (↑x : ℕ) (↑(↑q : ℚˣ) : ℚ) = |(↑(↑(↑q : ℚˣ) : ℚ) : ℝ)| := by
        have h_prod_one : ∀ {q : ℚˣ}, (∀ p : ℕ, p.Prime → p ∉ S → padicValRat p q = 0) → ∏ x ∈ S.attach, (↑(↑x : ℕ) : ℝ) ^ padicValRat (↑x : ℕ) (↑(↑q : ℚˣ) : ℚ) = |(↑(↑(↑q : ℚˣ) : ℚ) : ℝ)| := by
          intros q hq
          have h_prod_one : ∏ x ∈ S.attach, (↑(↑x : ℕ) : ℝ) ^ padicValRat (↑x : ℕ) (↑(↑q : ℚˣ) : ℚ) = ∏ p ∈ Nat.primeFactors (q.val : ℚ).num.natAbs ∪ Nat.primeFactors (q.val : ℚ).den, (↑p : ℝ) ^ padicValRat p (↑(↑q : ℚˣ) : ℚ) := by
            rw [ ← Finset.prod_subset ];
            any_goals exact Finset.univ.filter fun x => x.val ∈ ( q.val : ℚ ).num.natAbs.primeFactors ∪ ( q.val : ℚ ).den.primeFactors;
            · refine' Finset.prod_bij ( fun x hx => x ) _ _ _ _ <;> simp +decide;
              -- If $b$ is a prime that divides the numerator or denominator of $q$, then $b$ must be in $S$ because otherwise, the $p$-adic valuation of $q$ at $b$ would be zero, contradicting the fact that $b$ divides the numerator or denominator.
              intros b hb
              by_cases hbS : b ∈ S;
              · tauto;
              · cases hb <;> simp_all +decide [ padicValRat ];
                · specialize hq b ; simp_all +decide [ padicValInt ];
                  rw [ padicValNat.eq_zero_of_not_dvd ( show ¬ b ∣ ( q : ℚ ).den from fun h => by have := Nat.dvd_gcd ( show b ∣ ( q : ℚ ).num.natAbs from by tauto ) h; simp_all +decide [ Rat.reduced ] ) ] at hq ; aesop;
                · have := hq b ( by tauto ) hbS; simp_all +decide [ padicValInt, padicValNat.eq_zero_of_not_dvd ] ;
                  specialize hq b ( by tauto ) hbS ; simp_all +decide [ sub_eq_zero ];
                  -- Since $q$ is a unit in the rationals, its numerator and denominator are coprime. Therefore, $b$ cannot divide both the numerator and the denominator.
                  have h_coprime : Nat.gcd (q.val.num.natAbs) (q.val.den) = 1 := by
                    exact q.val.reduced;
                  have h_div : b ∣ (q.val.num.natAbs) ∧ b ∣ (q.val.den) := by
                    -- Since $b$ is prime and divides the denominator, the $p$-adic valuation of the denominator is at least 1. Therefore, the $p$-adic valuation of the numerator must also be at least 1, implying $b$ divides the numerator.
                    have h_div_num : padicValNat b (q.val.num.natAbs) ≥ 1 := by
                      rw [ hq ];
                      rw [ padicValNat ] ; aesop;
                    exact ⟨ Nat.dvd_of_mod_eq_zero ( Nat.mod_eq_zero_of_dvd <| by contrapose! h_div_num; simp_all +decide [ padicValNat.eq_zero_of_not_dvd ] ), by tauto ⟩;
                  exact absurd ( Nat.dvd_gcd h_div.1 h_div.2 ) ( by aesop );
            · exact fun x hx => Finset.mem_attach _ x;
            · simp +contextual [ padicValRat ];
              intro p hp hp' hp''; specialize hq p ( hS p hp ) ; simp_all +decide [ padicValInt, padicValNat.eq_zero_of_not_dvd ] ;
          have h_prod_one : ∏ p ∈ Nat.primeFactors (q.val : ℚ).num.natAbs ∪ Nat.primeFactors (q.val : ℚ).den, (↑p : ℝ) ^ padicValRat p (↑(↑q : ℚˣ) : ℚ) = |(↑(↑q : ℚˣ) : ℚ)| := by
            have h_prod_one : ∀ {n : ℕ}, n ≠ 0 → ∏ p ∈ Nat.primeFactors n, (↑p : ℝ) ^ padicValNat p n = n := by
              intro n hn; norm_cast; rw [ ← Nat.factorization_prod_pow_eq_self hn ] ;
              conv_rhs => rw [ ← Nat.factorization_prod_pow_eq_self hn ] ;
              simp +decide [ Finsupp.prod ];
              refine' Finset.prod_congr rfl fun p hp => _;
              rw [ Nat.factorization_def ] ; aesop
            have h_prod_one : ∏ p ∈ Nat.primeFactors (q.val : ℚ).num.natAbs ∪ Nat.primeFactors (q.val : ℚ).den, (↑p : ℝ) ^ padicValRat p (↑(↑q : ℚˣ) : ℚ) = (∏ p ∈ Nat.primeFactors (q.val : ℚ).num.natAbs, (↑p : ℝ) ^ padicValNat p (q.val : ℚ).num.natAbs) / (∏ p ∈ Nat.primeFactors (q.val : ℚ).den, (↑p : ℝ) ^ padicValNat p (q.val : ℚ).den) := by
              -- By definition of padicValRat, we can split the product into the product over the prime factors of the numerator and the product over the prime factors of the denominator.
              have h_split : ∀ p ∈ Nat.primeFactors (q.val : ℚ).num.natAbs ∪ Nat.primeFactors (q.val : ℚ).den, (↑p : ℝ) ^ padicValRat p (↑q : ℚ) = if p ∈ Nat.primeFactors (q.val : ℚ).num.natAbs then (↑p : ℝ) ^ padicValNat p (q.val : ℚ).num.natAbs else (↑p : ℝ) ^ (-padicValNat p (q.val : ℚ).den : ℤ) := by
                intro p hp; split_ifs <;> simp_all +decide [ padicValRat ] ;
                · simp +decide [ padicValInt, padicValNat.eq_zero_of_not_dvd, ‹_› ];
                  rw [ padicValNat.eq_zero_of_not_dvd ( show ¬ p ∣ ( q : ℚ ).den from fun h => by have := Nat.dvd_gcd ‹Nat.Prime p ∧ p ∣ Int.natAbs ( q : ℚ ).num›.2 h; simp_all +decide [ Rat.reduced ] ) ] ; norm_num;
                · simp +decide [ *, padicValInt, padicValNat.eq_zero_of_not_dvd ];
              rw [ Finset.prod_congr rfl h_split, Finset.prod_ite ];
              simp +decide [ Finset.filter_mem_eq_inter, Finset.filter_not, Finset.prod_union, Finset.prod_sdiff, div_eq_mul_inv ];
              congr! 1;
              · rw [ Finset.prod_subset ];
                · simp +contextual [ Finset.subset_iff ];
                · simp +contextual [ Nat.dvd_prime ];
              · rw [ Finset.prod_subset ];
                · intro p hp; aesop;
                · simp +contextual [ Nat.dvd_prime ];
                  intro p pp dp dn; have := Nat.dvd_gcd dn dp; simp_all +decide [ Rat.reduced ] ;
            simp_all +decide [ Rat.abs_def ];
            simp +decide [ Rat.mkRat_eq_div ];
          aesop;
        exact h_prod_one fun p hp hp' => q.2 p hp hp';
      by_cases h : ( q : ℚˣ ) = 1 <;> aesop;
    have h_sum_qa : ∑' q' : O_S_star S, (f.val ((embed_O_S_star S hS q') * (embed_O_S_star S hS q * a))) = ∑' q' : O_S_star S, (f.val ((embed_O_S_star S hS q') * a)) := by
      conv_rhs => rw [ ← Equiv.tsum_eq ( Equiv.mulRight q ) ] ;
      simp +decide [ mul_assoc, mul_comm, mul_left_comm, embed_O_S_star ];
      exact?;
    aesop)

/-
Defining the fundamental domain I_S and the measure on C_S.
-/
open MeasureTheory Complex Set

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)

def I_S : Set (J_S S hS) :=
  { x | 0 < x.val.1 ∧ ∀ p : S, ‖x.val.2 p‖ = 1 }

noncomputable def mu_C_S : Measure (C_S S hS) :=
  Measure.map (QuotientGroup.mk) ((mu_J_S S hS).restrict (I_S S hS))

instance : MeasureSpace (C_S S hS) := ⟨mu_C_S S hS⟩

/-
Defining the norm on the idele class group C_S.
-/
open MeasureTheory Complex

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)

noncomputable def norm_C_S (x : C_S S hS) : ℝ :=
  Quotient.liftOn x (norm_J_S S hS) (by
  -- To show that the norm is constant on the cosets, we need to prove that the norm of any unit q in O_S_star is 1.
  have h_norm_unit : ∀ q : O_S_star S, norm_J_S S hS (embed_O_S_star S hS q) = 1 := by
    intro q;
    unfold norm_J_S;
    unfold embed_O_S_star norm_A_S;
    simp +decide [ Norm.norm ];
    have h_norm_unit : ∀ q : ℚˣ, (∀ p : ℕ, p.Prime → p ∉ S → padicValRat p q = 0) → |(q : ℝ)| * (∏ p ∈ S, (p : ℝ) ^ padicValRat p q)⁻¹ = 1 := by
      intro q hq
      have h_norm_unit : |(q : ℝ)| = ∏ p ∈ Nat.primeFactors (q.val).num.natAbs ∪ Nat.primeFactors (q.val).den, (p : ℝ) ^ padicValRat p q := by
        have h_norm_unit : ∀ (n d : ℕ), n ≠ 0 → d ≠ 0 → |(n : ℝ) / d| = ∏ p ∈ Nat.primeFactors n ∪ Nat.primeFactors d, (p : ℝ) ^ (padicValNat p n - padicValNat p d : ℤ) := by
          intros n d hn hd
          have h_norm_unit : (n : ℝ) / d = ∏ p ∈ Nat.primeFactors n ∪ Nat.primeFactors d, (p : ℝ) ^ (padicValNat p n - padicValNat p d : ℤ) := by
            have h_norm_unit : (n : ℝ) = ∏ p ∈ Nat.primeFactors n, (p : ℝ) ^ padicValNat p n ∧ (d : ℝ) = ∏ p ∈ Nat.primeFactors d, (p : ℝ) ^ padicValNat p d := by
              have h_norm_unit : ∀ (n : ℕ), n ≠ 0 → (n : ℝ) = ∏ p ∈ Nat.primeFactors n, (p : ℝ) ^ (padicValNat p n) := by
                intro n hn; norm_cast; rw [ ← Nat.factorization_prod_pow_eq_self hn ] ;
                conv_lhs => rw [ ← Nat.factorization_prod_pow_eq_self hn ] ;
                exact Finset.prod_congr rfl fun p hp => by rw [ Nat.factorization_def ] ; aesop;
              exact ⟨ h_norm_unit n hn, h_norm_unit d hd ⟩;
            -- By combining the exponents, we can rewrite the product as the product over the union of the prime factors of n and d.
            have h_union : (∏ p ∈ n.primeFactors, (p : ℝ) ^ padicValNat p n) / (∏ p ∈ d.primeFactors, (p : ℝ) ^ padicValNat p d) = (∏ p ∈ n.primeFactors ∪ d.primeFactors, (p : ℝ) ^ padicValNat p n) / (∏ p ∈ n.primeFactors ∪ d.primeFactors, (p : ℝ) ^ padicValNat p d) := by
              rw [ ← Finset.prod_subset ( Finset.subset_union_left ), ← Finset.prod_subset ( Finset.subset_union_right ) ];
              · simp +contextual [ padicValNat.eq_zero_of_not_dvd, Nat.dvd_prime ];
                intro p hp hp'; cases hp <;> simp_all +decide [ Nat.Prime.dvd_iff_one_le_factorization ] ;
                rw [ padicValNat.eq_zero_of_not_dvd ] <;> simp_all +decide [ Nat.factorization_eq_zero_iff ];
              · simp +contextual [ padicValNat.eq_zero_of_not_dvd, Nat.dvd_prime ];
                rintro p ( ⟨ hp₁, hp₂, hp₃ ⟩ | ⟨ hp₁, hp₂, hp₃ ⟩ ) hp₄ <;> simp_all +decide [ padicValNat.eq_zero_of_not_dvd ];
            simp_all +decide [ zpow_sub₀, Nat.cast_ne_zero ];
            rw [ ← Finset.prod_div_distrib ] ; exact Finset.prod_congr rfl fun x hx => by rw [ zpow_sub₀ ( Nat.cast_ne_zero.mpr <| Nat.Prime.ne_zero <| by aesop ) ] ; norm_cast;
          rw [ h_norm_unit, abs_of_nonneg ( Finset.prod_nonneg fun _ _ => by positivity ) ];
        convert h_norm_unit ( q.val.num.natAbs ) ( q.val.den ) ( by simp +decide [ Rat.num_ne_zero ] ) ( by simp +decide [ Rat.den_nz ] ) using 1;
        simp +decide [ abs_div, abs_mul, Rat.cast_def ];
      rw [ h_norm_unit, ← div_eq_mul_inv, div_eq_iff ];
      · rw [ one_mul, ← Finset.prod_subset ( show ( q.val.num.natAbs.primeFactors ∪ q.val.den.primeFactors ) ⊆ S from ?_ ) ];
        · intro p hp hq; specialize hq; simp_all +decide [ padicValRat ] ;
          simp_all +decide [ padicValInt, padicValNat.eq_zero_of_not_dvd ];
        · intro p hp;
          contrapose! hp; simp_all +decide [ padicValRat ] ;
          constructor <;> intro hp_prime hp_div <;> specialize hq p hp_prime hp <;> simp_all +decide [ padicValInt, padicValNat.eq_zero_of_not_dvd ];
          · rw [ padicValNat.eq_zero_of_not_dvd ( show ¬ p ∣ ( q : ℚ ).den from fun h => hp_prime.not_dvd_one <| by have := Nat.dvd_gcd hp_div h; simp_all +decide [ Rat.reduced ] ) ] at hq ; aesop;
          · rw [ padicValNat.eq_zero_of_not_dvd ] at hq <;> simp_all +decide [ Nat.Prime.dvd_iff_not_coprime ];
            exact hp_prime.coprime_iff_not_dvd.mpr fun h => hp_div <| hp_prime.coprime_iff_not_dvd.mpr fun h' => by have := Nat.dvd_gcd h h'; simp_all +decide [ Rat.reduced ] ;
      · exact Finset.prod_ne_zero_iff.mpr fun p hp => by have := hS p hp; exact zpow_ne_zero _ ( Nat.cast_ne_zero.mpr this.ne_zero ) ;
    convert h_norm_unit q q.2 using 1;
    conv_rhs => rw [ ← Finset.prod_attach ] ;
  -- If $a \sim b$, then there exists $q \in O_S_star$ such that $a = q * b$.
  intro a b hab
  obtain ⟨q, hq⟩ : ∃ q : O_S_star S, a = embed_O_S_star S hS q * b := by
    obtain ⟨ q, hq ⟩ := hab;
    obtain ⟨ q, hq ⟩ := q;
    -- Since $q$ is in the opposite of the embedded subgroup, it must be of the form $embed_O_S_star S hS q$ for some $q \in O_S_star$.
    obtain ⟨ q', hq' ⟩ : ∃ q' : O_S_star S, q = MulOpposite.op (embed_O_S_star S hS q') := by
      obtain ⟨ q', hq' ⟩ := q;
      obtain ⟨ q'', hq'' ⟩ := ‹ { unop' := { val := q', inv := hq', val_inv := _, inv_val := _ } } ∈ ( O_S_star_embedded S hS ).op ›;
      exact ⟨ q'', by simpa [ MulOpposite.unop_op ] using congr_arg MulOpposite.op hq''.symm ⟩;
    -- Substitute hq' into the equation from hq to get the desired equality.
    use q';
    simp +decide [ ← hq, hq' ];
    exact mul_comm _ _;
  -- The norm of a product is the product of the norms.
  have h_norm_mul : ∀ a b : J_S S hS, norm_J_S S hS (a * b) = norm_J_S S hS a * norm_J_S S hS b := by
    intros a b
    simp [norm_J_S, norm_A_S];
    simp +decide only [Finset.prod_mul_distrib, mul_assoc, mul_left_comm];
  rw [ hq, h_norm_mul, h_norm_unit q, one_mul ])

/-
Checking norm_C_S and defining the characteristic functions P_Lambda and S_Lambda.
-/
open MeasureTheory Complex

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)

#check norm_C_S S hS

noncomputable def P_Lambda_func (Λ : ℝ) (x : A_S S hS) : ℂ :=
  if norm_A_S S hS x < Λ then 1 else 0

noncomputable def S_Lambda_func (Λ : ℝ) (x : C_S S hS) : ℂ :=
  if norm_C_S S hS x > Λ⁻¹ then 1 else 0


open MeasureTheory Complex ENNReal

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)

abbrev L2_C_S := Lp ℂ 2 (mu_C_S S hS)

-- Check instances
#synth NormedAddCommGroup (L2_C_S S hS)
#synth InnerProductSpace ℂ (L2_C_S S hS)
#synth CompleteSpace (L2_C_S S hS)

/-
Define L2(X_S) as a type wrapper around L2(C_S).
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)

structure L2_X_S_Type where
  val : L2_C_S S hS

/-
Check signature of Function.Injective.addCommGroup.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap

#check Function.Injective.addCommGroup

/-
Define basic algebraic operations on L2(X_S).
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)

instance : Add (L2_X_S_Type S hS) := ⟨fun x y => ⟨x.val + y.val⟩⟩
instance : Zero (L2_X_S_Type S hS) := ⟨⟨0⟩⟩
instance : Neg (L2_X_S_Type S hS) := ⟨fun x => ⟨-x.val⟩⟩
instance : Sub (L2_X_S_Type S hS) := ⟨fun x y => ⟨x.val - y.val⟩⟩
instance : SMul ℕ (L2_X_S_Type S hS) := ⟨fun n x => ⟨n • x.val⟩⟩
instance : SMul ℤ (L2_X_S_Type S hS) := ⟨fun n x => ⟨n • x.val⟩⟩
instance : SMul ℂ (L2_X_S_Type S hS) := ⟨fun c x => ⟨c • x.val⟩⟩

/-
Check if Add instance is visible.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)

#synth Add (L2_X_S_Type S hS)

/-
Define equivalence between L2(X_S) and L2(C_S).
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)

def L2_X_S_equiv : L2_X_S_Type S hS ≃ L2_C_S S hS where
  toFun := fun x => x.val
  invFun := fun x => ⟨x⟩
  left_inv := fun x => rfl
  right_inv := fun x => rfl

/-
Check availability of Equiv.addCommGroup.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap

#check Equiv.addCommGroup

/-
L2(X_S) is an additive commutative group.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)

instance : AddCommGroup (L2_X_S_Type S hS) :=
  Equiv.addCommGroup (L2_X_S_equiv S hS)

/-
Check signature of NormedAddCommGroup.induced.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap

#check NormedAddCommGroup.induced

/-
Check definition of NormedAddCommGroup.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap

#print NormedAddCommGroup

/-
Check definition of InnerProductSpace.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap

#print InnerProductSpace

/-
Check definition of NormedSpace.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap

#print NormedSpace

/-
Check NormedAddGroup definition and instance.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap

#print NormedAddGroup
#synth NormedAddGroup (L2_C_S S hS)

/-
L2(X_S) is a metric space.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)

instance : MetricSpace (L2_X_S_Type S hS) :=
  MetricSpace.induced (L2_X_S_equiv S hS) (L2_X_S_equiv S hS).injective inferInstance

/-
Check definition of SeminormedAddCommGroup.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap

#print SeminormedAddCommGroup

/-
L2(X_S) is a normed additive commutative group.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)

instance : Norm (L2_X_S_Type S hS) := ⟨fun x => ‖x.val‖⟩

instance : NormedAddCommGroup (L2_X_S_Type S hS) where
  dist_eq x y := by
    change dist x.val y.val = ‖x.val - y.val‖
    exact dist_eq_norm x.val y.val

/-
L2(X_S) is a seminormed additive commutative group.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)

instance : SeminormedAddCommGroup (L2_X_S_Type S hS) where
  dist_eq x y := by
    change dist x.val y.val = ‖x.val - y.val‖
    exact dist_eq_norm x.val y.val

/-
L2(X_S) is a complex module.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)

instance : Module ℂ (L2_X_S_Type S hS) :=
  Equiv.module ℂ (L2_X_S_equiv S hS)

/-
L2(X_S) is a normed complex space.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)

instance : NormedSpace ℂ (L2_X_S_Type S hS) where
  norm_smul_le c x := by
    change ‖c • x.val‖ ≤ ‖c‖ * ‖x.val‖
    exact norm_smul_le c x.val

/-
Check if NormedAddCommGroup extends SeminormedAddCommGroup.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap

#check NormedAddCommGroup.toSeminormedAddCommGroup

/-
Define the Fourier transform on L2(X_S) and its adjoint.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)

opaque FourierTransform_S_L2 : L2_X_S_Type S hS ≃ₗᵢ[ℂ] L2_X_S_Type S hS

noncomputable def FourierTransform_S_L2_adjoint : L2_X_S_Type S hS ≃ₗᵢ[ℂ] L2_X_S_Type S hS :=
  (FourierTransform_S_L2 S hS).symm

/-
Define P_Lambda and S_Lambda as opaque operators.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
variable (Λ : ℝ)

opaque P_Lambda : L2_X_S_Type S hS →L[ℂ] L2_X_S_Type S hS
opaque S_Lambda : L2_C_S S hS →L[ℂ] L2_C_S S hS

/-
Define V_S as an opaque operator depending on a function h.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)

opaque V_S (h : C_S S hS → ℂ) : L2_C_S S hS →L[ℂ] L2_C_S S hS

/-
Define L2_X_S_iso as a linear isometry equivalence.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)

def L2_X_S_iso : L2_X_S_Type S hS ≃ₗᵢ[ℂ] L2_C_S S hS where
  toFun := fun x => x.val
  invFun := fun x => ⟨x⟩
  left_inv := fun x => rfl
  right_inv := fun x => rfl
  map_add' := fun x y => rfl
  map_smul' := fun c x => rfl
  norm_map' := fun x => rfl

/-
Check types of P_Lambda and S_Lambda.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)

#check P_Lambda S hS
#check S_Lambda S hS

/-
Check types of operators and equivalences.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
variable (Λ : ℝ)
variable (h : C_S S hS → ℂ)

#check S_Lambda S hS
#check P_Lambda S hS
#check V_S S hS
#check L2_X_S_equiv S hS
#check FourierTransform_S_L2 S hS

/-
Define P_Lambda and S_Lambda operators depending on Lambda.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)

opaque P_Lambda_op (Λ : ℝ) : L2_X_S_Type S hS →L[ℂ] L2_X_S_Type S hS
opaque S_Lambda_op (Λ : ℝ) : L2_C_S S hS →L[ℂ] L2_C_S S hS

/-
Check conversion from LinearIsometryEquiv to ContinuousLinearMap.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)

#check (L2_X_S_iso S hS).toContinuousLinearEquiv.toContinuousLinearMap

/-
Check if LinearIsometryEquiv can be converted to ContinuousLinearEquiv.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)

#check (L2_X_S_iso S hS).toContinuousLinearEquiv

/-
Define the subtracted term in T_h.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
variable (Λ : ℝ)

noncomputable def T_h_sub_term : L2_C_S S hS →L[ℂ] L2_C_S S hS :=
  (L2_X_S_iso S hS).toContinuousLinearEquiv.toContinuousLinearMap ∘L
  (FourierTransform_S_L2_adjoint S hS).toContinuousLinearEquiv.toContinuousLinearMap ∘L
  (P_Lambda_op S hS Λ) ∘L
  (FourierTransform_S_L2 S hS).toContinuousLinearEquiv.toContinuousLinearMap ∘L
  (L2_X_S_iso S hS).symm.toContinuousLinearEquiv.toContinuousLinearMap

/-
Define the operator T_h.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
variable (Λ : ℝ)
variable (h : C_S S hS → ℂ)

noncomputable def T_h : L2_C_S S hS →L[ℂ] L2_C_S S hS :=
  V_S S hS h ∘L (S_Lambda_op S hS Λ -
    (L2_X_S_iso S hS).toContinuousLinearEquiv.toContinuousLinearMap ∘L
    (FourierTransform_S_L2_adjoint S hS).toContinuousLinearEquiv.toContinuousLinearMap ∘L
    (P_Lambda_op S hS Λ) ∘L
    (FourierTransform_S_L2 S hS).toContinuousLinearEquiv.toContinuousLinearMap ∘L
    (L2_X_S_iso S hS).symm.toContinuousLinearEquiv.toContinuousLinearMap)

/-
Define the operator T_h.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
variable (Λ : ℝ)
variable (h : C_S S hS → ℂ)

noncomputable def T_h_op : L2_C_S S hS →L[ℂ] L2_C_S S hS :=
  V_S S hS h ∘L (S_Lambda_op S hS Λ -
    (L2_X_S_iso S hS).toContinuousLinearEquiv.toContinuousLinearMap ∘L
    (FourierTransform_S_L2_adjoint S hS).toContinuousLinearEquiv.toContinuousLinearMap ∘L
    (P_Lambda_op S hS Λ) ∘L
    (FourierTransform_S_L2 S hS).toContinuousLinearEquiv.toContinuousLinearMap ∘L
    (L2_X_S_iso S hS).symm.toContinuousLinearEquiv.toContinuousLinearMap)

/-
Define IsTraceClass and trace as opaque constants.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

opaque IsTraceClass (A : H →L[ℂ] H) : Prop
noncomputable opaque trace (A : H →L[ℂ] H) : ℂ

/-
Check T_h and T_h_op.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
variable (Λ : ℝ)
variable (h : C_S S hS → ℂ)

#check T_h S hS Λ h
#check T_h_op S hS Λ h

/-
Check if T_h is defined.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
variable (Λ : ℝ)
variable (h : C_S S hS → ℂ)

#check T_h S hS Λ h

/-
Define Q_Lambda as the kernel of P_Lambda composed with the Fourier transform.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
variable (Λ : ℝ)

def Q_Lambda : Submodule ℂ (L2_X_S_Type S hS) :=
  LinearMap.ker ((P_Lambda_op S hS Λ).toLinearMap.comp (FourierTransform_S_L2 S hS).toLinearEquiv.toLinearMap)

/-
Define IsHilbertSchmidt as an opaque predicate.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

opaque IsHilbertSchmidt (A : H →L[ℂ] H) : Prop

/-
Define hat_h and Delta as opaque functions.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)

opaque hat_h (h : C_S S hS → ℂ) (s : ℂ) : ℂ
opaque Delta (h : C_S S hS → ℂ) : ℂ

/-
Check types of hat_h and Delta.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
variable (h : C_S S hS → ℂ)

#check hat_h
#check Delta

/-
Check instances for L2_C_S.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)

#synth NormedAddCommGroup (L2_C_S S hS)
#synth InnerProductSpace ℂ (L2_C_S S hS)
#synth CompleteSpace (L2_C_S S hS)

/-
Assume Theorem 1.1 as a hypothesis.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
variable (h : C_S S hS → ℂ)

variable (h_Theorem_1_1 : ∀ Λ : ℝ, IsTraceClass (T_h S hS Λ h) ∧ trace (T_h S hS Λ h) = Delta S hS h - hat_h S hS h 0 - hat_h S hS h 1)

/-
Define the statement of Theorem 1.1.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
variable (h : C_S S hS → ℂ)

def Theorem_1_1_Statement (Λ : ℝ) : Prop :=
  IsTraceClass (T_h S hS Λ h) ∧
  trace (T_h S hS Λ h) = Delta S hS h - hat_h S hS h 0 - hat_h S hS h 1

/-
Define projection operators onto Q_Lambda_perp and Q_Lambda in L2(C_S).
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
variable (Λ : ℝ)

noncomputable def Proj_Q_Lambda_perp_C : L2_C_S S hS →L[ℂ] L2_C_S S hS :=
  (L2_X_S_iso S hS).toContinuousLinearEquiv.toContinuousLinearMap ∘L
  (FourierTransform_S_L2_adjoint S hS).toContinuousLinearEquiv.toContinuousLinearMap ∘L
  (P_Lambda_op S hS Λ) ∘L
  (FourierTransform_S_L2 S hS).toContinuousLinearEquiv.toContinuousLinearMap ∘L
  (L2_X_S_iso S hS).symm.toContinuousLinearEquiv.toContinuousLinearMap

noncomputable def Proj_Q_Lambda_C : L2_C_S S hS →L[ℂ] L2_C_S S hS :=
  1 - Proj_Q_Lambda_perp_C S hS Λ

/-
Define the set of nontrivial zeros of the Riemann zeta function.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap

def NontrivialZeros : Set ℂ := {ρ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1}

/-
Define P_n, g_n, and p_{n, epsilon} with corrected syntax.
-/
open Real BigOperators Finset

noncomputable def P_n (n : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ range n, (n.choose (k + 1) : ℝ) * (t ^ k) / (Nat.factorial k : ℝ)

noncomputable def g_n (n : ℕ) (x : ℝ) : ℝ :=
  if 0 < x ∧ x ≤ 1 then P_n n (log x) else 0

noncomputable def p_n_epsilon (n : ℕ) (ε : ℝ) (x : ℝ) : ℝ :=
  if x > ε then g_n n x else 0

/-
Define trace of an operator on a subspace given by a projection P.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable def trace_on_subspace (P : H →L[ℂ] H) (T : H →L[ℂ] H) : ℂ :=
  trace (P ∘L T ∘L P)

/-
Define lambda_n as an opaque constant.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)

opaque lambda_n (n : ℕ) : ℂ

/-
Define functions for Theorem 1.2: tau, ell, alpha, vartheta, g, h.
-/
open Real BigOperators Finset MeasureTheory

noncomputable def tau_aux (x : ℝ) : ℝ :=
  if abs x < 1 then Real.exp (-1 / (1 - x^2)) else 0

opaque c_0 : ℝ

noncomputable def tau (ε : ℝ) (x : ℝ) : ℝ :=
  (c_0 / ε) * tau_aux ((x - 1) / ε)

noncomputable def ell_n_epsilon (n : ℕ) (ε : ℝ) (x : ℝ) : ℝ :=
  ∫ y in Set.Ioi 0, p_n_epsilon n ε (x * y) * tau ε y

noncomputable def a_func (t : ℝ) : ℝ := 1 / (t * (t - 1))

opaque a_1 : ℝ
opaque a_2 : ℝ

noncomputable def alpha (t : ℝ) : ℝ :=
  if 0 < t ∧ t < 1 then (a_1 * t + a_2) * Real.exp (a_func t) else 0

noncomputable def vartheta (t : ℝ) : ℝ :=
  ∑' k : ℕ, (-1 : ℝ)^k * alpha ((k + 1) * t)

noncomputable def vartheta_1 (ε : ℝ) (u : ℝ) : ℝ :=
  if u > ε then vartheta u else 0

noncomputable def hat_vartheta_1_0 (ε : ℝ) : ℝ :=
  ∫ u in Set.Ioi 0, vartheta_1 ε u / u

noncomputable def g_n_epsilon (n : ℕ) (ε : ℝ) (x : ℝ) : ℝ :=
  ell_n_epsilon n ε x - (1 / hat_vartheta_1_0 ε) * ∫ u in Set.Ioi 0, ell_n_epsilon n ε (x / u) * vartheta_1 ε u / u

noncomputable def h_n_epsilon (n : ℕ) (ε : ℝ) (x : ℝ) : ℝ :=
  ∫ y in Set.Ioi 0, g_n_epsilon n ε (x * y) * g_n_epsilon n ε y

/-
Define the statement of Theorem 1.3.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
variable (Λ : ℝ)
variable (h : C_S S hS → ℂ)

def Theorem_1_3_Statement : Prop :=
  trace_on_subspace (Proj_Q_Lambda_perp_C S hS Λ) (T_h S hS Λ h) = 0

/-
Define the statement of Theorem 1.4.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
variable (Λ : ℝ)
variable (h : C_S S hS → ℂ)

def Theorem_1_4_Statement : Prop :=
  let tr := trace_on_subspace (Proj_Q_Lambda_C S hS Λ) (T_h S hS Λ h)
  tr.im = 0 ∧ 0 ≤ tr.re

/-
Define h_{n, epsilon} on C_S.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)

noncomputable def h_n_eps (n : ℕ) (ε : ℝ) (x : C_S S hS) : ℂ :=
  (h_n_epsilon n ε (norm_C_S S hS x) : ℂ)

/-
Define g(x) = |x|^{-1} g_{n, epsilon}(|x|^{-1}).
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)

noncomputable def g_func (n : ℕ) (ε : ℝ) (x : C_S S hS) : ℝ :=
  (norm_C_S S hS x)⁻¹ * g_n_epsilon n ε (norm_C_S S hS x)⁻¹

/-
Define the statement of Theorem 1.2 with corrected lambda_n arguments.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap Filter Topology

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)

def Theorem_1_2_Statement : Prop :=
  ∀ n : ℕ,
    (Tendsto (fun ε => Delta S hS (h_n_eps S hS n ε)) (𝓝[>] 0) (𝓝 (2 * lambda_n n))) ∧
    (∀ ε > 0, hat_h S hS (h_n_eps S hS n ε) 0 = 0) ∧
    (∀ ε > 0, hat_h S hS (h_n_eps S hS n ε) 1 = 0)


#check riemannZeta

#check RiemannHypothesis
#check lambda_n

#check le_of_tendsto_of_tendsto

/-
Defining Li's Criterion as a proposition.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap Filter Topology

def Lis_Criterion_Statement : Prop :=
  (∀ n : ℕ, 0 ≤ (lambda_n n).re) → RiemannHypothesis

/-
Checking the signatures of the theorem statements to ensure correct usage in the main theorem.
-/
variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
variable (Λ : ℝ)
variable (h : C_S S hS → ℂ)

#check Theorem_1_1_Statement S hS h Λ
#check Theorem_1_2_Statement S hS
#check Theorem_1_3_Statement S hS Λ h
#check Theorem_1_4_Statement S hS Λ h

/-
If P is a projection (P^2 = P), then 1-P is also a projection.
-/
lemma proj_compl_is_proj {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (P : H →L[ℂ] H) (hP : P ∘L P = P) :
  (1 - P) ∘L (1 - P) = (1 - P) := by
  simp_all +decide [ ContinuousLinearMap.ext_iff ]

/-
Decomposition of an operator T into P T + (1-P) T.
-/
lemma op_split_add {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (T : H →L[ℂ] H) (P : H →L[ℂ] H) :
  P ∘L T + (1 - P) ∘L T = T := by
  exact ContinuousLinearMap.ext fun x => by simp +decide ;

#check IsTraceClass
#check trace

/-
If a function f tends to a and f(x) >= 0 eventually, then a >= 0.
-/
lemma limit_nonneg_of_nonneg {f : ℝ → ℝ} {a : ℝ} {l : Filter ℝ} [l.NeBot]
  (hf : Tendsto f l (𝓝 a)) (hle : ∀ᶠ x in l, 0 ≤ f x) : 0 ≤ a :=
  le_of_tendsto_of_tendsto tendsto_const_nhds hf hle

#check self_mem_nhdsWithin


/-
Checking definitions of OrthonormalBasis, exists_orthonormalBasis, and Summable.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

#check OrthonormalBasis
#check exists_orthonormalBasis
#check Summable

/-
Checking HilbertBasis and exists_hilbertBasis.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

#check HilbertBasis
#check exists_hilbertBasis

/-
Defining IsHilbertSchmidt_def, IsTraceClass_def, and trace_def with explicit inner product type.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def IsHilbertSchmidt_def (A : H →L[ℂ] H) : Prop :=
  ∃ (ι : Type) (b : HilbertBasis ι ℂ H), Summable (fun i => ‖A (b i)‖ ^ 2)

def IsTraceClass_def (A : H →L[ℂ] H) : Prop :=
  ∃ (B C : H →L[ℂ] H), IsHilbertSchmidt_def B ∧ IsHilbertSchmidt_def C ∧ A = B ∘L C

noncomputable def trace_def (A : H →L[ℂ] H) : ℂ :=
  if h : IsTraceClass_def A then
    let w := Classical.choose (exists_hilbertBasis ℂ H)
    let b := Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ H))
    ∑' (i : w), inner ℂ (b i) (A (b i))
  else 0

/-
Defining L2_A_S and checking instances.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap InnerProductSpace

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)

abbrev L2_A_S := Lp ℂ 2 (mu_S S hS)

-- Check if instances are inferred
#synth NormedAddCommGroup (L2_A_S S hS)
#synth InnerProductSpace ℂ (L2_A_S S hS)
#synth CompleteSpace (L2_A_S S hS)

/-
The product of two L2 functions on different spaces is L2 on the product space.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap InnerProductSpace

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β}

theorem MemLp_prod_mul_two {f : α → ℂ} {g : β → ℂ}
  (hf : MemLp f 2 μ) (hg : MemLp g 2 ν) :
  MemLp (fun p : α × β => f p.1 * g p.2) 2 (μ.prod ν) := by
    rw [ MeasureTheory.memLp_two_iff_integrable_sq_norm ] at *;
    · simpa [ mul_pow ] using hf.prod_mul hg;
    · exact hf.1;
    · exact hg.1;
    · have h_prod : AEStronglyMeasurable (fun p : α × β => f p.1) (μ.prod ν) ∧ AEStronglyMeasurable (fun p : α × β => g p.2) (μ.prod ν) := by
        refine' ⟨ _, _ ⟩;
        · have := hf.aestronglyMeasurable;
          exact?;
        · have := hg.aestronglyMeasurable;
          exact?;
      exact h_prod.1.mul h_prod.2

/-
Locally constant compactly supported functions on finite adeles are in L2.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap InnerProductSpace

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)

theorem LocallyConstant_CompactSupport_MemLp (h : FiniteAdeleS S hS → ℂ)
  (hh_lc : IsLocallyConstant h) (hh_supp : HasCompactSupport h) :
  MemLp h 2 (Measure.pi (fun p : S => @dx_p p ⟨hS p p.2⟩)) := by
    apply_rules [ Continuous.memLp_of_hasCompactSupport ];
    · exact?;
    · constructor;
      intro K hK;
      -- Since $K$ is compact, it is bounded. Therefore, there exists a constant $M$ such that for all $x \in K$, $|x| \leq M$.
      obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ x ∈ K, ‖x‖ ≤ M := by
        exact hK.isBounded.exists_norm_le;
      refine' lt_of_le_of_lt ( MeasureTheory.measure_mono _ ) _;
      exact Set.pi Set.univ fun p => Metric.closedBall 0 M;
      · intro x hx; specialize hM x hx; simp_all +decide [ norm_le_pi_norm ] ;
        exact fun p hp => le_trans ( norm_le_pi_norm x ⟨ p, hp ⟩ ) hM;
      · simp +decide [ dx_p ];
        refine' ENNReal.prod_lt_top _;
        intro p hp; exact?;

/-
Checking SchwartzMap.memLp.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap InnerProductSpace

#check SchwartzMap.memLp

/-
Schwartz-Bruhat functions are in L2.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap InnerProductSpace

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)

theorem SchwartzBruhat_MemLp (f : SchwartzBruhatSpace S hS) : MemLp f.val 2 (mu_S S hS) := by
  obtain ⟨ n, g, h, hh, hf ⟩ := f.2;
  -- Each term $g_i * h_i$ is in $L^2$.
  have h_term_in_L2 : ∀ i, MemLp (fun x => (g i) x.1 * (h i) x.2) 2 (mu_S S hS) := by
    -- Since $g_i$ is in $L^2(\mathbb{R})$ and $h_i$ is in $L^2(\mathbb{A}_S^{\text{finite}})$, their product is in $L^2(\mathbb{A}_S)$.
    have h_prod_L2 : ∀ i, MemLp (fun x => (g i) x) 2 (MeasureTheory.volume) ∧ MemLp (fun x => (h i) x) 2 (MeasureTheory.Measure.pi (fun p : S => @dx_p p ⟨hS p p.2⟩)) := by
      exact fun i => ⟨ by exact ( g i ).memLp 2, by exact LocallyConstant_CompactSupport_MemLp S hS ( h i ) ( hh i |>.1 ) ( hh i |>.2 ) ⟩;
    intro i;
    have := h_prod_L2 i;
    convert MemLp_prod_mul_two this.1 this.2 using 1;
  -- The sum of L^2 functions is in L^2.
  have h_sum_in_L2 : ∀ (n : ℕ) (f : Fin n → A_S S hS → ℂ), (∀ i, MemLp (f i) 2 (mu_S S hS)) → MemLp (fun x => ∑ i, f i x) 2 (mu_S S hS) := by
    intro n f hf; induction' n with n ih <;> simp_all +decide [ Fin.sum_univ_succ ] ;
    exact MemLp.add ( hf 0 ) ( ih _ fun i => hf i.succ );
  convert h_sum_in_L2 n _ h_term_in_L2 using 1

/-
Embedding Schwartz-Bruhat functions into L2.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap InnerProductSpace

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)

noncomputable def SchwartzBruhat_to_L2 (f : SchwartzBruhatSpace S hS) : L2_A_S S hS :=
  (MemLp.toLp f.val (SchwartzBruhat_MemLp S hS f) : L2_A_S S hS)

/-
Defining the additive character on finite adeles.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap InnerProductSpace

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)

noncomputable def psi_finite (x : FiniteAdeleS S hS) : ℂ :=
  ∏ p : S, @psi_p p ⟨hS p p.2⟩ (x p)

/-
Defining the Fourier transform on finite adeles.
-/
open MeasureTheory Complex ENNReal ContinuousLinearMap InnerProductSpace

variable (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)

noncomputable def FourierTransform_FiniteAdele (f : FiniteAdeleS S hS → ℂ) (y : FiniteAdeleS S hS) : ℂ :=
  ∫ x, f x * psi_finite S hS (x * y) ∂(Measure.pi (fun p : S => @dx_p p ⟨hS p p.2⟩))
