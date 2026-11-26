import AxiomGuard

namespace RotatorCalculusPaper

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 6400000

/-- **Theorem 18 (Two-Arc Pillai–Wronskian Trajectory Composition & Cycle Chord Law, `0 Prop premises`)**: -/
theorem thm18_arbitrary_modulus_rotator_and_two_arc_trajectory_wronskian
    (P1 Q1 P2 Q2 n_start n_mid n_final : Int) :
    let D1 := P1 * n_mid - Q1 * n_start
    let D2 := P2 * n_final - Q2 * n_mid
    let C1 := P1 - Q1
    let C2 := P2 - Q2
    let Ctot := P1 * P2 - Q1 * Q2
    let Dtot := Q2 * D1 + P1 * D2
    ((P1 * P2) * n_final - (Q1 * Q2) * n_start = Dtot) ∧
    (Ctot = Q2 * C1 + P1 * C2 ∧ Ctot = P2 * C1 + Q1 * C2) ∧
    ((P1 * P2) * (n_final - n_start) + Ctot * n_start = Dtot) ∧
    (n_final = n_start →
      (Ctot * n_start = Q2 * D1 + P1 * D2) ∧
      (Ctot * n_mid   = P2 * D1 + Q1 * D2) ∧
      (Ctot * (n_mid - n_start) = C2 * D1 - C1 * D2)) := by
  dsimp
  have hComp : ((P1 * P2) * n_final - (Q1 * Q2) * n_start) -
               (Q2 * (P1 * n_mid - Q1 * n_start) + P1 * (P2 * n_final - Q2 * n_mid)) = 0 := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  have hDisp1 : ((P1 * P2) * (n_final - n_start) + (P1 * P2 - Q1 * Q2) * n_start) -
                ((P1 * P2) * n_final - (Q1 * Q2) * n_start) = 0 := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  have hCycMid : ((P1 * P2 - Q1 * Q2) * n_mid) -
                 (P2 * (P1 * n_mid - Q1 * n_start) + Q1 * (P2 * n_final - Q2 * n_mid)) =
                 (Q1 * P2) * (n_start - n_final) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  have hWronsk : ((P1 * P2 - Q1 * Q2) * (n_mid - n_start)) -
                 ((P2 - Q2) * (P1 * n_mid - Q1 * n_start) - (P1 - Q1) * (P2 * n_final - Q2 * n_mid)) =
                 ((Q1 - P1) * P2) * (n_start - n_final) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  refine ⟨by omega,
          ⟨by simp only [Int.mul_sub, Int.sub_mul, Int.mul_comm, Int.mul_left_comm]; omega,
           by simp only [Int.mul_sub, Int.sub_mul, Int.mul_comm, Int.mul_left_comm]; omega⟩,
          by omega, ?_⟩
  intro hCycle
  have e3 : n_start - n_final = 0 := by omega
  have e4 : n_final - n_start = 0 := by omega
  rw [e4] at hDisp1
  rw [e3] at hCycMid hWronsk
  exact ⟨by omega, by omega, by omega⟩

/-- **Theorem 19 (Unimodular `SL₂(ℤ)` Catalan Exponent-Basis Decomposition `u = 2a - 3b, v = 2b - a`
and Sign-Free Strictly Positive Cycle Wronskian Sum)**: -/
theorem thm19_collatz_catalan_sl2_basis_drift_bounds_and_positive_wronskian_sum
    (a b P1 Q1 P2 Q2 n_start n_mid n_final D1 D2 : Int) :
    let u := 2 * a - 3 * b
    let v := 2 * b - a
    let G1 := P1 - Q1
    let G2 := Q2 - P2
    let Ctot := P1 * P2 - Q1 * Q2
    (2 * 2 - 3 * 1 = 1 ∧ 2 * u + 3 * v = a ∧ u + 2 * v = b ∧ u + v = a - b) ∧
    (Ctot = P2 * G1 - Q1 * G2 ∧ Ctot = Q2 * G1 - P1 * G2) ∧
    (P1 * n_mid - Q1 * n_start = D1 → P2 * n_final - Q2 * n_mid = D2 → n_final = n_start →
      (Ctot * (n_start - n_mid) = G2 * D1 + G1 * D2) ∧
      (Ctot > 0 → G2 * D1 + G1 * D2 > 0 → n_start > n_mid)) := by
  dsimp
  refine ⟨⟨by omega, by omega, by omega, by omega⟩,
          ⟨by simp only [Int.mul_sub, Int.sub_mul, Int.mul_comm, Int.mul_left_comm]; omega,
           by simp only [Int.mul_sub, Int.sub_mul, Int.mul_comm, Int.mul_left_comm]; omega⟩, ?_⟩
  intro hArc1 hArc2 hCycle
  have hPosSum : ((P1 * P2 - Q1 * Q2) * (n_start - n_mid)) - ((Q2 - P2) * D1 + (P1 - Q1) * D2) =
                 (Q2 - P2) * (P1 * n_mid - Q1 * n_start - D1) -
                 (Q1 - P1) * (P2 * n_final - Q2 * n_mid - D2) +
                 ((Q1 - P1) * P2) * (n_final - n_start) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  have e1 : P1 * n_mid - Q1 * n_start - D1 = 0 := by omega
  have e2 : P2 * n_final - Q2 * n_mid - D2 = 0 := by omega
  have e3 : n_final - n_start = 0 := by omega
  rw [e1, e2, e3] at hPosSum
  refine ⟨by omega, ?_⟩
  intro hCtot hSumPos
  by_cases hLe : n_start - n_mid ≤ 0
  · have := Int.mul_nonpos_of_nonneg_of_nonpos (by omega : P1 * P2 - Q1 * Q2 ≥ 0) hLe; omega
  · omega

/-- **Theorem 20 (Planetary Cyclic Drift Shift Law `p_k D_tot^{(k+1)} - q_gear D_tot^{(k)} = P_tot - Q_tot`)**: -/
theorem thm20_collatz_dual_drift_tower_and_cyclic_shift_law
    (qGear pk pk1 Premk Qprev Bprev D2k D2k1 nk : Int) :
    let Ptot := pk * Premk
    let Qtot := qGear * Qprev
    let Ctot := Ptot - Qtot
    let Dtot_k  := Qprev + pk * D2k
    let Dtot_k1 := Premk + qGear * D2k
    (pk * Dtot_k1 - qGear * Dtot_k = Ctot) ∧
    (Dtot_k1 = Qprev + pk1 * D2k1 → pk1 * D2k1 - qGear * D2k = Premk - Qprev) ∧
    (Ctot * nk = Dtot_k → pk * (D2k - (Qprev - Bprev)) ≥ 0 →
      Ctot * nk ≥ Qprev + pk * (Qprev - Bprev)) := by
  dsimp
  refine ⟨by simp only [Int.mul_add, Int.add_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega,
          by omega, ?_⟩
  intro _ _; have : pk * (D2k - (Qprev - Bprev)) = pk * D2k - pk * (Qprev - Bprev) := by simp only [Int.mul_sub]
  omega

/-- **Theorem 21 (Uniqueness of the Planetary Gear Stationary Point `(p_k - q_gear) n* = 1 ⟹ (p_k = q_gear + 1 ∧ n* = 1)`
and Exact Differential Closure Criterion `Q n_start + D_{a,b} = P` for Reaching `n_final = 1`)**: -/
theorem thm21_collatz_planetary_stationary_point_uniqueness_and_reachability_criterion
    (qGear pk nStar P Q n_start n_final Dab : Int) :
    (nStar ≥ 1 → (pk - qGear) * nStar = 1 → pk = qGear + 1 ∧ nStar = 1) ∧
    (P * n_final - Q * n_start = Dab →
      P * (n_final - 1) = (Q * n_start + Dab) - P ∧
      (n_final = 1 → Q * n_start + Dab = P) ∧
      (P ≠ 0 → Q * n_start + Dab = P → n_final = 1)) := by
  refine ⟨?_, ?_⟩
  · intro hN hStat
    have hPos : pk - qGear ≥ 1 := by
      by_cases h : pk - qGear ≤ 0
      · have := Int.mul_nonpos_of_nonpos_of_nonneg h (by omega : nStar ≥ 0); omega
      · omega
    have hDiff : (pk - qGear) * nStar - nStar = (pk - qGear - 1) * nStar := by simp only [Int.sub_mul, Int.one_mul]
    have hGe0 : (pk - qGear - 1) * nStar ≥ 0 := Int.mul_nonneg (by omega) (by omega)
    have hN1 : nStar = 1 := by omega
    rw [hN1, Int.mul_one] at hStat; exact ⟨by omega, hN1⟩
  · intro hEq
    have hDist : P * (n_final - 1) - ((Q * n_start + Dab) - P) = (P * n_final - Q * n_start) - Dab := by
      simp only [Int.mul_sub, Int.mul_one]; omega
    refine ⟨by omega, by intro h1; rw [h1, Int.mul_one] at hEq; omega, ?_⟩
    intro hPne0 hClose
    cases Int.mul_eq_zero.mp (by omega : P * (n_final - 1) = 0) with
    | inl hP => exact False.elim (hPne0 hP)
    | inr hN => omega

/-- **Theorem 22 (Arbitrary-Stage Fermat Infinite-Descent Reduction `(P - Q) n > D_{a,b} ↔ n_final < n`,
Symmetric Group `S_b` Adjacent-Transposition Monotonicity, and the Two-Policemen Permutation Squeeze, `0 non-order Prop premises`)**: -/
theorem thm22_collatz_arbitrary_stage_fermat_descent_reduction
    (P Q Pb Pab wk pk pk1 Drest n n_final : Int)
    (hP : P > 0) :
    let Dab := P * n_final - Q * n
    let C := P - Q
    let Dorig := Drest + wk * pk
    let Dswap := Drest + wk * pk1
    let Dmin  := Q - Pb
    let Dmax  := Pab * (Q - Pb)
    (P * (n - n_final) = C * n - Dab ∧ (C * n > Dab ↔ n_final < n)) ∧
    (Dswap - Dorig = wk * (pk1 - pk) ∧ (wk > 0 → (pk < pk1 ↔ Dorig < Dswap))) ∧
    (P = Pab * Pb → Dmin ≤ Dab → Dab ≤ Dmax →
      Q * (n + 1) - Pb ≤ P * n_final ∧
      P * n_final ≤ Q * (n + Pab) - P ∧
      P * (n - n_final) ≥ P * (n + 1) - Q * (n + Pab)) ∧
    (C > 0 → n_final = n → P - Q ≤ Dab → Dab ≤ P - Q → n = 1) := by
  dsimp
  have hId : P * (n - n_final) - ((P - Q) * n - (P * n_final - Q * n)) = 0 := by
    simp only [Int.mul_sub, Int.sub_mul]; omega
  have hEquiv : (P - Q) * n > P * n_final - Q * n ↔ n_final < n := by
    constructor
    · intro hGt
      by_cases hLe : n - n_final ≤ 0
      · have := Int.mul_nonpos_of_nonneg_of_nonpos (by omega : P ≥ 0) hLe; omega
      · omega
    · intro hLt; have := Int.mul_pos hP (by omega : n - n_final > 0); omega
  refine ⟨⟨by omega, hEquiv⟩, ⟨by simp only [Int.mul_sub]; omega, ?_⟩, ?_, ?_⟩
  · intro hWkPos
    have hSwapId : (Drest + wk * pk1) - (Drest + wk * pk) = wk * (pk1 - pk) := by simp only [Int.mul_sub]; omega
    constructor
    · intro hLt; have := Int.mul_pos hWkPos (by omega : pk1 - pk > 0); omega
    · intro hDLt
      by_cases hLe : pk1 - pk ≤ 0
      · have := Int.mul_nonpos_of_nonneg_of_nonpos (by omega : wk ≥ 0) hLe; omega
      · omega
  · intro hPprod hDmin hDmax
    have hL : (P * n_final) - (Q * (n + 1) - Pb) = (P * n_final - Q * n) - (Q - Pb) := by
      simp only [Int.mul_add, Int.mul_one]; omega
    have hR : (Q * (n + Pab) - P) - (P * n_final) =
              (Pab * (Q - Pb) - (P * n_final - Q * n)) + (Pab * Pb - P) + (Q * Pab - Pab * Q) := by
      simp only [Int.mul_add, Int.mul_sub]; omega
    have hCommQP : Q * Pab = Pab * Q := Int.mul_comm Q Pab
    have hDescSq : P * (n - n_final) - (P * (n + 1) - Q * (n + Pab)) = (Q * (n + Pab) - P) - (P * n_final) := by
      simp only [Int.mul_sub, Int.mul_add, Int.mul_one]; omega
    exact ⟨by omega, by omega, by omega⟩
  · intro hCpos hCyc hGe hLe
    have hCyc1 : (P - Q) * (n - 1) = (P * n_final - Q * n) - (P - Q) - P * (n_final - n) := by
      simp only [Int.mul_sub, Int.sub_mul, Int.mul_one]; omega
    have hSub0 : n_final - n = 0 := by omega
    rw [hSub0, Int.mul_zero] at hCyc1
    cases Int.mul_eq_zero.mp (by omega : (P - Q) * (n - 1) = 0) with
    | inl hC0 => omega
    | inr hn1 => omega

/-- **Theorem 23 (Dead-End-Free `q_gear`-Adic Prefix Decomposition `D_{a,b} = P_{pen} + q_gear D_{b-1}`
and `2 P_{tot}` 2-Adic Construction Modulus)**: -/
theorem thm23_collatz_dead_end_free_ternary_prefix_closure
    (qGear Ppen plast Qprev Dprev n n_prime Ptot Dab kb kb_prime : Int) :
    let Qtot := qGear * Qprev
    let Dtot := Ppen + qGear * Dprev
    (Dtot - Ppen = qGear * Dprev) ∧
    (Qtot * n + Dtot = Ppen * plast ↔ Ppen * (plast - 1) = qGear * (Qprev * n + Dprev)) ∧
    (Qtot * n + Dab = Ptot * (2 * kb + 1) →
     Qtot * n_prime + Dab = Ptot * (2 * kb_prime + 1) →
      Qtot * n + Dab = (2 * Ptot) * kb + Ptot ∧
      Qtot * (n - n_prime) = (2 * Ptot) * (kb - kb_prime)) := by
  dsimp
  have hId : (qGear * Qprev * n + (Ppen + qGear * Dprev) - Ppen * plast) =
             (qGear * (Qprev * n + Dprev) - Ppen * (plast - 1)) := by
    simp only [Int.mul_add, Int.mul_sub, Int.mul_one, Int.mul_assoc]; omega
  refine ⟨by omega, ⟨fun _ => by omega, fun _ => by omega⟩, ?_⟩
  intro h1 h2
  have hExpand1 : Ptot * (2 * kb + 1) = (2 * Ptot) * kb + Ptot := by
    simp only [Int.mul_add, Int.mul_one, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have hExpand2 : Ptot * (2 * kb_prime + 1) = (2 * Ptot) * kb_prime + Ptot := by
    simp only [Int.mul_add, Int.mul_one, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have hDiff : (qGear * Qprev) * (n - n_prime) - (2 * Ptot) * (kb - kb_prime) =
               ((qGear * Qprev) * n - (2 * Ptot) * kb) - ((qGear * Qprev) * n_prime - (2 * Ptot) * kb_prime) := by
    simp only [Int.mul_sub]; omega
  exact ⟨by omega, by omega⟩

/-- **Theorem 24 (Counter-Rotating Forward-Backward Planetary Gear Splice in `ℤ_{P_1} × ℤ_{Q_2}`,
Bézout Meeting-Point Reconstruction, and Pure-Driven Sikorsky Chord Law, `0 Prop premises`)**: -/
theorem thm24_collatz_counter_rotating_forward_backward_splice_and_bezout_lock
    (P1 Q1 P2 Q2 n_start n_mid u v : Int) :
    let D1 := P1 * n_mid - Q1 * n_start
    let D2 := P2 - Q2 * n_mid
    let dBez := P1 * v - Q2 * u
    (Q2 * (Q1 * n_start + D1) = P1 * (P2 - D2) ∧
     (Q1 * Q2) * n_start + (Q2 * D1 + P1 * D2) = P1 * P2) ∧
    (dBez * n_mid = v * (Q1 * n_start + D1) - u * (P2 - D2)) ∧
    ((Q1 * Q2) * (n_start - n_mid) = (P1 - Q1) * (P2 - D2) - Q2 * D1) := by
  dsimp
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;>
    (simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
                Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; try omega)

/-- **Theorem 25 (Planetary Gear-Tooth Meshing `q_gear n_0 + c_tooth = p_0 n_1`
and Inductive Step-Peeling Law)**: -/
theorem thm25_collatz_automatic_2adic_3adic_gear_tooth_meshing_and_step_peeling
    (qGear cTooth Qprev p0 Prem Drem n0 n1 : Int) :
    ((qGear * Qprev) * n0 + (cTooth * Qprev + p0 * Drem) = p0 * Prem ↔
      Qprev * (qGear * n0 + cTooth) = p0 * (Prem - Drem)) ∧
    (p0 ≠ 0 → qGear * n0 + cTooth = p0 * n1 →
      ((qGear * Qprev) * n0 + (cTooth * Qprev + p0 * Drem) = p0 * Prem ↔ Qprev * n1 + Drem = Prem)) := by
  have hId1 : ((qGear * Qprev) * n0 + (cTooth * Qprev + p0 * Drem) - p0 * Prem) =
              (Qprev * (qGear * n0 + cTooth) - p0 * (Prem - Drem)) := by
    simp only [Int.mul_add, Int.mul_sub, Int.mul_one, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  refine ⟨⟨fun _ => by omega, fun _ => by omega⟩, ?_⟩
  intro hp0 hStep
  have hId2 := hId1; rw [hStep] at hId2
  have hFactor : Qprev * (p0 * n1) - p0 * (Prem - Drem) = p0 * (Qprev * n1 + Drem - Prem) := by
    simp only [Int.mul_add, Int.mul_sub, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  constructor
  · intro _
    cases Int.mul_eq_zero.mp (by omega : p0 * (Qprev * n1 + Drem - Prem) = 0) with
    | inl h0 => exact False.elim (hp0 h0)
    | inr hRem => omega
  · intro h
    have hRem0 : Qprev * n1 + Drem - Prem = 0 := by omega
    rw [hRem0, Int.mul_zero] at hFactor; omega

/-- **Theorem 26 (Single-Step Planetary Wronskian Excess Identity
`(q_gear n_ref + c_tooth) n_k - p_k n_ref n_{k+1} = c_tooth (n_k - n_ref)` and Bernoulli–Euler Drift Bound, `0 Prop premises`)**: -/
theorem thm26_collatz_step_wronskian_excess_identity_and_bernoulli_euler_cycle_lock
    (qGear pk nk nk1 nref Ptot Qtot n0PowPrev n0 nfinal Dab Bpow : Int) :
    let cTooth := pk * nk1 - qGear * nk
    ((qGear * nref + cTooth) * nk - pk * nref * nk1 = cTooth * (nk - nref)) ∧
    (Ptot * nfinal = Qtot * n0 + Dab →
     Ptot * n0PowPrev * nfinal ≤ Bpow →
      n0PowPrev * Dab ≤ Bpow - Qtot * (n0PowPrev * n0) ∧
      Ptot * n0PowPrev * (n0 - nfinal) ≥ Ptot * (n0PowPrev * n0) - Bpow) := by
  dsimp
  have hWronsk : (qGear * nref + (pk * nk1 - qGear * nk)) * nk - pk * nref * nk1 =
                 (pk * nk1 - qGear * nk) * (nk - nref) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  refine ⟨hWronsk, ?_⟩
  intro hTraj hBern
  have hSub : Ptot * n0PowPrev * nfinal = n0PowPrev * (Ptot * nfinal) := by
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  rw [hTraj] at hSub
  have hExpand : n0PowPrev * (Qtot * n0 + Dab) = Qtot * (n0PowPrev * n0) + n0PowPrev * Dab := by
    simp only [Int.mul_add, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have hDiff : Ptot * n0PowPrev * (n0 - nfinal) = Ptot * (n0PowPrev * n0) - Ptot * n0PowPrev * nfinal := by
    simp only [Int.mul_sub, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  exact ⟨by omega, by omega⟩

/-- **Theorem 27 (Pure-Binary Balance Over the Stationary Root `n_ref = n* = 1`,
Dual-Drift Conservation Law `D_{a,b} + E_{a,b} = (F_{tot} - Q_{tot}) n_0`, and Upper-Ceiling Screw `(U_d, U_+)`, `0 Prop premises`)**: -/
theorem thm27_collatz_pure_binary_stationary_excess_law_and_dual_drift_conservation
    (Ptot Qtot Ftot m0 mb : Int) :
    let n0    := m0 + m0 + 1
    let nb    := mb + mb + 1
    let Dab   := Ptot * nb - Qtot * n0
    let Eab   := Ftot * n0 - Ptot * nb
    let Ud    := Ftot * m0 - Ptot * mb
    let Uplus := Ptot * (mb + 1) - Ftot * (m0 + 1)
    let Splus := Ptot * (mb + 1) - Qtot * (m0 + 1)
    (Dab + Eab = (Ftot - Qtot) * n0 ∧ Ptot * (n0 - nb) = Eab - (Ftot - Ptot) * n0) ∧
    (Ud + Uplus = Ptot - Ftot ∧
     Ud - Uplus = Eab ∧
     Splus + Ud = (Ftot - Qtot) * m0 + (Ptot - Qtot)) := by
  dsimp
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;>
    (simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul, Int.mul_one, Int.one_mul,
                Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; try omega)

/-- **Theorem 28 (Willis Carrier Differential Balance `z_1(ω_1 - ω_H) + z_2(ω_2 - ω_H) = 0`,
Centered Coordinate `m_k = (n_k - 1)/2`, and Two-Axle Differential Rotor Duality `S_+ + S_d = P_{tot} - Q_{tot}`)**: -/
theorem thm28_collatz_centered_stationary_coordinate_and_gear_deviation_law
    (qHalf pk phalf mk mk1 Ptot Qtot n0 nb m0 mb Dab Sd Splus Pr0 q0 Splus_red z1 z2 w1 w2 wH : Int) :
    let qGear := 2 * qHalf + 1
    let nk  := 2 * mk + 1
    let nk1 := 2 * mk1 + 1
    (z1 * (w1 - wH) + z2 * (w2 - wH) = (z1 * w1 + z2 * w2) - (z1 + z2) * wH) ∧
    (pk = 2 * phalf → pk * nk1 = qGear * nk + 1 →
      pk * mk1 - qGear * mk = (qHalf + 1) - phalf) ∧
    (n0 = 2 * m0 + 1 → nb = 2 * mb + 1 →
     Ptot * nb - Qtot * n0 = Dab →
     Sd = Qtot * m0 - Ptot * mb →
     Splus = Ptot * (mb + 1) - Qtot * (m0 + 1) →
      (Splus + Sd = Ptot - Qtot ∧ Splus - Sd = Dab ∧ Qtot * m0 - Sd = Ptot * mb) ∧
      (m0 + 1 = Pr0 * q0 → Splus = Pr0 * Splus_red →
        Ptot * (m0 - mb) = Pr0 * ((Ptot - Qtot) * q0 - Splus_red))) := by
  dsimp
  have hWillis : z1 * (w1 - wH) + z2 * (w2 - wH) = (z1 * w1 + z2 * w2) - (z1 + z2) * wH := by
    simp only [Int.mul_sub, Int.add_mul]; omega
  have hStepCentered : (2 * phalf) * (2 * mk1 + 1) - ((2 * qHalf + 1) * (2 * mk + 1) + 1) =
                       2 * ((2 * phalf) * mk1 - (2 * qHalf + 1) * mk - ((qHalf + 1) - phalf)) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul, Int.mul_one, Int.one_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  refine ⟨hWillis, by intro hpk _; rw [hpk] at *; omega, ?_⟩
  intro hn0 hnb hTraj hSd hSplus
  have hSum : (Ptot * (mb + 1) - Qtot * (m0 + 1)) + (Qtot * m0 - Ptot * mb) = Ptot - Qtot := by
    simp only [Int.mul_add, Int.mul_one]; omega
  have h2m0 : 2 * m0 + 1 = m0 + m0 + 1 := by omega
  have h2mb : 2 * mb + 1 = mb + mb + 1 := by omega
  have hDiff : (Ptot * (mb + 1) - Qtot * (m0 + 1)) - (Qtot * m0 - Ptot * mb) =
               Ptot * (mb + mb + 1) - Qtot * (m0 + m0 + 1) := by
    simp only [Int.mul_add, Int.mul_one]; omega
  rw [← h2m0, ← h2mb, ← hn0, ← hnb, hTraj] at hDiff
  have hDesc : Ptot * (m0 - mb) - ((Ptot - Qtot) * (m0 + 1) - (Ptot * (mb + 1) - Qtot * (m0 + 1))) = 0 := by
    simp only [Int.mul_sub, Int.sub_mul, Int.mul_add, Int.mul_one]; omega
  refine ⟨⟨by omega, by omega, by omega⟩, ?_⟩
  intro hm0Core hSplusCore
  have hRed : (Ptot - Qtot) * (Pr0 * q0) - Pr0 * Splus_red = Pr0 * ((Ptot - Qtot) * q0 - Splus_red) := by
    simp only [Int.mul_sub, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  rw [← hm0Core, ← hSplusCore] at hRed
  omega

/-- Cumulative binary exponent `A_M = ∑_{m=0}^{M-1} (β_m + r_{m+1} + 1)` across `M` macro-steps. -/
def macroSumA : List (Int × Int) → Int
  | [] => 0
  | (beta, rNext) :: rest => (beta + rNext + 1) + macroSumA rest

/-- Cumulative ternary exponent `B_M = ∑_{m=0}^{M-1} (r_m + 1)` starting from `r_0`. -/
def macroSumB : Int → List (Int × Int) → Int
  | _, [] => 0
  | rCurr, (_, rNext) :: rest => (rCurr + 1) + macroSumB rNext rest

/-- Total even-reset exponent sum `∑_{m=0}^{M-1} β_m` across `M` macro-steps. -/
def macroSumBeta : List (Int × Int) → Int
  | [] => 0
  | (beta, _) :: rest => beta + macroSumBeta rest

/-- Final trailing-ones count `r_M` after `M` macro-steps starting from `r_0`. -/
def macroFinalR : Int → List (Int × Int) → Int
  | rCurr, [] => rCurr
  | _, (_, rNext) :: rest => macroFinalR rNext rest

/-- Cumulative Catalan descent drift `∑_{m=0}^{M-1} (2 β_m - 1 - r_m)` across `M` macro-steps. -/
def macroCatalanDrift : Int → List (Int × Int) → Int
  | _, [] => 0
  | rCurr, (beta, rNext) :: rest => (2 * beta - 1 - rCurr) + macroCatalanDrift rNext rest

/-- Total binary gear pitch `P_tot(L) = ∏_{(P, Q, D) ∈ L} P` of an arbitrary `M`-screw cascade `L`. -/
def multiScrewP : List (Int × Int × Int) → Int
  | [] => 1
  | (p, _, _) :: rest => p * multiScrewP rest

/-- Total ternary gear pitch `Q_tot(L) = ∏_{(P, Q, D) ∈ L} Q` of an arbitrary `M`-screw cascade `L`. -/
def multiScrewQ : List (Int × Int × Int) → Int
  | [] => 1
  | (_, q, _) :: rest => q * multiScrewQ rest

/-- Composite gap modulus `C_tot(L) = P_tot(L) - Q_tot(L)` of an arbitrary `M`-screw cascade `L`. -/
def multiScrewC (screws : List (Int × Int × Int)) : Int :=
  multiScrewP screws - multiScrewQ screws

/-- Composite planetary drift accumulator `D_tot(L)` of an arbitrary `M`-screw cascade `L`. -/
def multiScrewD : List (Int × Int × Int) → Int
  | [] => 0
  | (p, _, d) :: rest => multiScrewQ rest * d + p * multiScrewD rest

theorem multiScrewP_append (L1 L2 : List (Int × Int × Int)) :
    multiScrewP (L1 ++ L2) = multiScrewP L1 * multiScrewP L2 := by
  induction L1 with
  | nil => dsimp [multiScrewP]; omega
  | cons hd tl ih => rcases hd with ⟨p, q, d⟩; dsimp [multiScrewP]; rw [ih]; simp only [Int.mul_assoc]

theorem multiScrewQ_append (L1 L2 : List (Int × Int × Int)) :
    multiScrewQ (L1 ++ L2) = multiScrewQ L1 * multiScrewQ L2 := by
  induction L1 with
  | nil => dsimp [multiScrewQ]; omega
  | cons hd tl ih => rcases hd with ⟨p, q, d⟩; dsimp [multiScrewQ]; rw [ih]; simp only [Int.mul_assoc]

theorem multiScrewD_append (L1 L2 : List (Int × Int × Int)) :
    multiScrewD (L1 ++ L2) = multiScrewQ L2 * multiScrewD L1 + multiScrewP L1 * multiScrewD L2 := by
  induction L1 with
  | nil => dsimp [multiScrewD, multiScrewP]; simp only [Int.mul_zero, Int.zero_add, Int.one_mul]
  | cons hd tl ih =>
    rcases hd with ⟨p, q, d⟩; dsimp [multiScrewD, multiScrewP]; rw [multiScrewQ_append, ih]
    simp only [Int.mul_add, Int.add_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega

/-- **Theorem 29 (Unified Multi-Screw Planetary Cascade Monoid, Double `SL₂(ℤ)` Bézout Lock,
Exclusion of the `2`-Adic Boundary Fixed Point `n_∞ = -1 ∉ ℕ`, Odd-Core Seesaw Law,
and Closed-Form `M`-Step Recurrence Solution with Dual-Core Drift Conservation, `0 Prop premises`)**: -/
theorem thm29_collatz_trailing_ones_burn_macro_step
    (steps : List (Int × Int))
    (L1 L2 : List (Int × Int × Int))
    (r0 PR QR PR_next pbeta q0 q1 n1 nInf : Int) :
    let n0    := PR * q0 - 1
    let dMac  := (pbeta * n1 + 1) - QR * q0
    let dn1   := (n1 + 1) - PR_next * q1
    -- 1. M-screw monoid homomorphism across screw lists L1, L2
    --    and stage-exponent telescoping:
    (multiScrewP (L1 ++ L2) = multiScrewP L1 * multiScrewP L2 ∧
     multiScrewQ (L1 ++ L2) = multiScrewQ L1 * multiScrewQ L2 ∧
     multiScrewD (L1 ++ L2) = multiScrewQ L2 * multiScrewD L1 + multiScrewP L1 * multiScrewD L2 ∧
     multiScrewC (L1 ++ L2) = multiScrewP L2 * multiScrewC L1 + multiScrewQ L1 * multiScrewC L2 ∧
     macroSumA steps - macroSumB r0 steps = macroSumBeta steps + macroFinalR r0 steps - r0 ∧
     2 * macroSumA steps - 3 * macroSumB r0 steps =
       macroCatalanDrift r0 steps + 2 * macroFinalR r0 steps - 2 * r0 ∧
     128 * macroSumA steps - 203 * macroSumB r0 steps =
       53 * (2 * macroSumA steps - 3 * macroSumB r0 steps) -
       22 * (2 * macroSumB r0 steps - macroSumA steps) ∧
     128 * macroSumA steps - 203 * macroSumB r0 steps =
       53 * macroCatalanDrift r0 steps +
       22 * (macroSumBeta steps - macroSumB r0 steps) +
       128 * (macroFinalR r0 steps - r0) ∧
     (multiScrewD L1 = multiScrewQ L1 - multiScrewP L1 →
       multiScrewD ((2, 3, 1) :: L1) = multiScrewQ ((2, 3, 1) :: L1) - multiScrewP ((2, 3, 1) :: L1)) ∧
     multiScrewD ((pbeta, 1, 0) :: L1) = pbeta * multiScrewD L1 ∧
     multiScrewP (L1 ++ [(pbeta, 1, 0)]) = multiScrewP L1 * pbeta ∧
     multiScrewQ (L1 ++ [(pbeta, 1, 0)]) = multiScrewQ L1 ∧
     multiScrewD (L1 ++ [(pbeta, 1, 0)]) = multiScrewD L1 ∧
     multiScrewD (L1 ++ [(pbeta, 1, 0), (PR, QR, QR - PR)] ++ L2) -
       multiScrewD (L1 ++ [(PR, QR, QR - PR), (pbeta, 1, 0)] ++ L2) =
       multiScrewP L1 * ((pbeta - 1) * (QR - PR) * multiScrewQ L2)) ∧
    -- 2. Double SL₂(ℤ) Bézout lock, exclusion of the non-natural 2-adic boundary fixed point n_∞ = -1 ∉ ℕ_{≥ 1},
    --    and macro-screw capture:
    ((PR ≠ QR → ((PR - QR) * nInf = QR - PR ↔ nInf = -1)) ∧
     (PR * q0 - n0 = 1) ∧
     ((PR * pbeta) * n1 - QR * n0 - (QR - PR) = PR * dMac) ∧
     ((PR * pbeta) * (n0 - n1) = PR * ((PR * pbeta - QR) * q0 - (pbeta - 1) - dMac))) ∧
    -- 3. Odd-Core transition and single-step dual envelope identity:
    (((pbeta * PR_next) * q1 - QR * q0 - (pbeta - 1) = dMac - pbeta * dn1) ∧
     ((QR + pbeta - 1) * q0 - (pbeta * PR_next) * q1 - (pbeta - 1) * (q0 - 1) = pbeta * dn1 - dMac) ∧
     (PR * pbeta - (QR + pbeta - 1) = (PR - 1) * pbeta - (QR - 1))) := by
  dsimp
  have hP := multiScrewP_append L1 L2
  have hQ := multiScrewQ_append L1 L2
  have hD := multiScrewD_append L1 L2
  have hC : multiScrewC (L1 ++ L2) = multiScrewP L2 * multiScrewC L1 + multiScrewQ L1 * multiScrewC L2 := by
    unfold multiScrewC; rw [hP, hQ]
    simp only [Int.mul_sub, Int.sub_mul, Int.mul_comm, Int.mul_left_comm]; omega
  have hTel1 : ∀ (st : List (Int × Int)) (rInit : Int),
        macroSumA st - macroSumB rInit st = macroSumBeta st + macroFinalR rInit st - rInit := by
    intro st; induction st with
    | nil => intro rInit; dsimp [macroSumA, macroSumB, macroSumBeta, macroFinalR]; omega
    | cons hd tl ih => intro rInit; rcases hd with ⟨b, rN⟩; dsimp [macroSumA, macroSumB, macroSumBeta, macroFinalR]; have := ih rN; omega
  have hTel2 : ∀ (st : List (Int × Int)) (rInit : Int),
        2 * macroSumA st - 3 * macroSumB rInit st = macroCatalanDrift rInit st + 2 * macroFinalR rInit st - 2 * rInit := by
    intro st; induction st with
    | nil => intro rInit; dsimp [macroSumA, macroSumB, macroCatalanDrift, macroFinalR]; omega
    | cons hd tl ih => intro rInit; rcases hd with ⟨b, rN⟩; dsimp [macroSumA, macroSumB, macroCatalanDrift, macroFinalR]; have := ih rN; omega
  refine ⟨⟨hP, hQ, hD, hC, hTel1 steps r0, hTel2 steps r0, by omega,
            by have h1 := hTel1 steps r0; have h2 := hTel2 steps r0; omega,
            by intro hUp; dsimp [multiScrewD, multiScrewQ, multiScrewP]; omega,
            by dsimp [multiScrewD]; omega,
            by rw [multiScrewP_append]; dsimp [multiScrewP]; simp only [Int.mul_one],
            by rw [multiScrewQ_append]; dsimp [multiScrewQ]; omega,
            by rw [multiScrewD_append]; dsimp [multiScrewQ, multiScrewD]; omega,
            by
              rw [multiScrewD_append, multiScrewD_append, multiScrewD_append, multiScrewD_append]
              rw [multiScrewP_append, multiScrewP_append]
              dsimp [multiScrewP, multiScrewQ, multiScrewD]
              simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
                         Int.mul_zero, Int.zero_mul, Int.add_zero, Int.zero_add,
                         Int.mul_one, Int.one_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
              omega⟩,
          ⟨?_, by omega,
           by simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul, Int.mul_one, Int.one_mul,
                         Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega,
           by simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul, Int.mul_one, Int.one_mul,
                         Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega⟩,
          ⟨by simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul, Int.mul_one, Int.one_mul,
                         Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega,
           by simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul, Int.mul_one, Int.one_mul,
                         Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega,
           by simp only [Int.sub_mul, Int.one_mul]; omega⟩⟩
  · intro hNe
    constructor
    · intro hEq
      have hZeroProd : (PR - QR) * (nInf + 1) = 0 := by
        have : (PR - QR) * (nInf + 1) = (PR - QR) * nInf - (QR - PR) := by simp only [Int.mul_add, Int.mul_one]; omega
        omega
      cases Int.mul_eq_zero.mp hZeroProd with
      | inl h0 => omega
      | inr h1 => omega
    · intro hMin1; subst hMin1; simp only [Int.mul_neg, Int.mul_one]; omega

/-- Elementary Collatz gear selected by a boolean step:
`true ↦ 𝒢_odd = (2, 3, 1)` (`2 n' = 3 n + 1`), `false ↦ 𝒢_even = (2, 1, 0)` (`2 n' = n`). -/
def collatzGearOfBool (b : Bool) : Int × Int × Int :=
  if b then (2, 3, 1) else (2, 1, 0)

/-- Multi-screw cascade `L(w)` generated by an arbitrary binary gear word `w : List Bool`. -/
def collatzWordScrews : List Bool → List (Int × Int × Int)
  | [] => []
  | b :: rest => collatzGearOfBool b :: collatzWordScrews rest

/-- Binary factor `2^B` accumulated across the odd gears (`true`) of `w : List Bool`. -/
def collatzWordPOdd : List Bool → Int
  | [] => 1
  | true :: rest => 2 * collatzWordPOdd rest
  | false :: rest => collatzWordPOdd rest

/-- Binary factor `2^(A - B)` accumulated across the even gears (`false`) of `w : List Bool`. -/
def collatzWordPEven : List Bool → Int
  | [] => 1
  | true :: rest => collatzWordPEven rest
  | false :: rest => 2 * collatzWordPEven rest

theorem collatzWordScrews_append (w1 w2 : List Bool) :
    collatzWordScrews (w1 ++ w2) = collatzWordScrews w1 ++ collatzWordScrews w2 := by
  induction w1 with
  | nil => rfl
  | cons b tl ih => dsimp [collatzWordScrews]; rw [ih]

theorem collatzWordPOdd_append (w1 w2 : List Bool) :
    collatzWordPOdd (w1 ++ w2) = collatzWordPOdd w1 * collatzWordPOdd w2 := by
  induction w1 with
  | nil => dsimp [collatzWordPOdd]; omega
  | cons b tl ih =>
    cases b <;> dsimp [collatzWordPOdd] <;> rw [ih]
    · simp only [Int.mul_assoc]

theorem collatzWordPEven_append (w1 w2 : List Bool) :
    collatzWordPEven (w1 ++ w2) = collatzWordPEven w1 * collatzWordPEven w2 := by
  induction w1 with
  | nil => dsimp [collatzWordPEven]; omega
  | cons b tl ih =>
    cases b <;> dsimp [collatzWordPEven] <;> rw [ih]
    · simp only [Int.mul_assoc]

/-- **Theorem 31 (Countable Binary Gear-Word Extremal Drift Envelope `3^B - 2^B ≤ R_w ≤ 2^{A-B}(3^B - 2^B)`
and Permutation-Free Cycle Squeeze across `w : List Bool`)**:
For every binary gear word `w : List Bool` (`P_w = 2^A`, `Q_w = 3^B`, `P_odd = 2^B`, `P_even = 2^{A-B}`,
`R_w = multiScrewD (collatzWordScrews w)`):
1. **Exact Factorization and Monotonicity:**
   `1 ≤ P_odd`, `1 ≤ P_even`, `P_odd ≤ Q_w`, `P_odd * P_even = P_w`, and `0 ≤ R_w`.
2. **Extremal Drift Envelope across All Words `w : List Bool`:**
   Regardless of the internal permutation of odd and even gears inside `w`, the screw remainder `R_w`
   is trapped between the all-odd-left minimum `3^B - 2^B` and the all-odd-right maximum `2^{A-B}(3^B - 2^B)`:
   `Q_w - P_odd ≤ R_w ∧ R_w ≤ P_even * (Q_w - P_odd) ∧ P_even * (Q_w - P_odd) = P_even * Q_w - P_w`.
3. **Permutation-Free Cycle Squeeze Law:**
   On any closed cycle `(P_w - Q_w) * n₀ = R_w`:
   - `Q_w - P_odd ≤ (P_w - Q_w) * n₀ ∧ (P_w - Q_w) * n₀ ≤ P_even * (Q_w - P_odd)`,
   - `Q_w * (n₀ + 1) ≤ P_w * n₀ + P_odd ∧ P_w * (n₀ + 1) ≤ Q_w * (n₀ + P_even)`,
   - in the centered stationary coordinate `u(n₀) = 2 n₀ + 1`:
     `P_w + Q_w - 2 * P_odd ≤ (P_w - Q_w) * (2 * n₀ + 1) ∧ (P_w - Q_w) * (2 * n₀ + 1) ≤ (2 * P_even - 1) * Q_w - P_w`,
   - if `w` contains at least one odd gear (`P_odd < Q_w`) and `1 ≤ n₀`, then `1 ≤ R_w` and `Q_w < P_w` (`3^B < 2^A`),
   - for `(P_w, Q_w, P_odd, P_even) = (4, 3, 2, 2)` (`A = 2, B = 1`), any odd cycle start (`n₀ % 2 = 1`) is uniquely `n₀ = 1`. -/
theorem thm31_collatz_binary_gear_word_extremal_drift_envelope_and_cycle_squeeze
    (w : List Bool) (n0 : Int) :
    let L := collatzWordScrews w
    let Pw := multiScrewP L
    let Qw := multiScrewQ L
    let Rw := multiScrewD L
    let Podd := collatzWordPOdd w
    let Peven := collatzWordPEven w
    (1 ≤ Podd ∧ 1 ≤ Peven ∧ Podd ≤ Qw ∧ Podd * Peven = Pw ∧ 0 ≤ Rw) ∧
    (Qw - Podd ≤ Rw ∧ Rw ≤ Peven * (Qw - Podd) ∧ Peven * (Qw - Podd) = Peven * Qw - Pw) ∧
    ((Pw - Qw) * n0 = Rw →
      (Qw - Podd ≤ (Pw - Qw) * n0 ∧ (Pw - Qw) * n0 ≤ Peven * (Qw - Podd)) ∧
      (Qw * (n0 + 1) ≤ Pw * n0 + Podd ∧ Pw * (n0 + 1) ≤ Qw * (n0 + Peven)) ∧
      (Pw + Qw - 2 * Podd ≤ (Pw - Qw) * (2 * n0 + 1) ∧
       (Pw - Qw) * (2 * n0 + 1) ≤ (2 * Peven - 1) * Qw - Pw) ∧
      (Podd < Qw → 1 ≤ n0 → 1 ≤ Rw ∧ Qw < Pw) ∧
      (Pw = 4 → Qw = 3 → Podd = 2 → Peven = 2 → n0 % 2 = 1 → n0 = 1)) := by
  have hInd : ∀ (l : List Bool),
      let Ll := collatzWordScrews l
      let Pl := multiScrewP Ll
      let Ql := multiScrewQ Ll
      let Rl := multiScrewD Ll
      let Poddl := collatzWordPOdd l
      let Pevenl := collatzWordPEven l
      1 ≤ Poddl ∧ 1 ≤ Pevenl ∧ Poddl ≤ Ql ∧ Poddl * Pevenl = Pl ∧
      Ql - Poddl ≤ Rl ∧ Rl ≤ Pevenl * (Ql - Poddl) := by
    intro l
    induction l with
    | nil =>
      dsimp [collatzWordScrews, multiScrewP, multiScrewQ, multiScrewD, collatzWordPOdd, collatzWordPEven]
      refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    | cons b tl ih =>
      rcases ih with ⟨hPo1, hPe1, hPoQ, hProd, hLow, hHigh⟩
      cases b with
      | false =>
        dsimp [collatzWordScrews, collatzGearOfBool, multiScrewP, multiScrewQ, multiScrewD,
               collatzWordPOdd, collatzWordPEven]
        simp only [Int.one_mul, Int.mul_zero, Int.zero_add]
        have hProdNext : collatzWordPOdd tl * (2 * collatzWordPEven tl) = 2 * multiScrewP (collatzWordScrews tl) := by
          rw [← hProd]; simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
        have hHighNext : 2 * multiScrewD (collatzWordScrews tl) ≤
                         (2 * collatzWordPEven tl) * (multiScrewQ (collatzWordScrews tl) - collatzWordPOdd tl) := by
          have : (2 * collatzWordPEven tl) * (multiScrewQ (collatzWordScrews tl) - collatzWordPOdd tl) =
                 2 * (collatzWordPEven tl * (multiScrewQ (collatzWordScrews tl) - collatzWordPOdd tl)) := by
            simp only [Int.mul_assoc]
          omega
        refine ⟨hPo1, by omega, hPoQ, hProdNext, by omega, hHighNext⟩
      | true =>
        dsimp [collatzWordScrews, collatzGearOfBool, multiScrewP, multiScrewQ, multiScrewD,
               collatzWordPOdd, collatzWordPEven]
        have hProdNext : (2 * collatzWordPOdd tl) * collatzWordPEven tl = 2 * multiScrewP (collatzWordScrews tl) := by
          rw [← hProd]; simp only [Int.mul_assoc]
        have hQlePeQ : multiScrewQ (collatzWordScrews tl) ≤
                       collatzWordPEven tl * multiScrewQ (collatzWordScrews tl) := by
          have hDiff : collatzWordPEven tl * multiScrewQ (collatzWordScrews tl) -
                       multiScrewQ (collatzWordScrews tl) =
                       (collatzWordPEven tl - 1) * multiScrewQ (collatzWordScrews tl) := by
            simp only [Int.sub_mul, Int.one_mul]
          have hNonneg : 0 ≤ (collatzWordPEven tl - 1) * multiScrewQ (collatzWordScrews tl) :=
            Int.mul_nonneg (by omega) (by omega)
          omega
        have hHighNext : multiScrewQ (collatzWordScrews tl) * 1 + 2 * multiScrewD (collatzWordScrews tl) ≤
                         collatzWordPEven tl * (3 * multiScrewQ (collatzWordScrews tl) - 2 * collatzWordPOdd tl) := by
          have hExpand : collatzWordPEven tl * (3 * multiScrewQ (collatzWordScrews tl) - 2 * collatzWordPOdd tl) =
                         collatzWordPEven tl * multiScrewQ (collatzWordScrews tl) +
                         2 * (collatzWordPEven tl * (multiScrewQ (collatzWordScrews tl) - collatzWordPOdd tl)) := by
            simp only [Int.mul_sub, Int.mul_add, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
            omega
          omega
        refine ⟨by omega, hPe1, by omega, hProdNext, by omega, hHighNext⟩
  dsimp
  rcases hInd w with ⟨hPo1, hPe1, hPoQ, hProd, hLow, hHigh⟩
  have hPeExpand : collatzWordPEven w * (multiScrewQ (collatzWordScrews w) - collatzWordPOdd w) =
                   collatzWordPEven w * multiScrewQ (collatzWordScrews w) - multiScrewP (collatzWordScrews w) := by
    have : collatzWordPEven w * (multiScrewQ (collatzWordScrews w) - collatzWordPOdd w) =
           collatzWordPEven w * multiScrewQ (collatzWordScrews w) - collatzWordPOdd w * collatzWordPEven w := by
      simp only [Int.mul_sub, Int.mul_comm (collatzWordPEven w) (collatzWordPOdd w)]
    rw [this, hProd]
  refine ⟨⟨hPo1, hPe1, hPoQ, hProd, by omega⟩, ⟨hLow, hHigh, hPeExpand⟩, ?_⟩
  intro hCyc
  have hB1 : multiScrewQ (collatzWordScrews w) - collatzWordPOdd w ≤
             (multiScrewP (collatzWordScrews w) - multiScrewQ (collatzWordScrews w)) * n0 := by omega
  have hB2 : (multiScrewP (collatzWordScrews w) - multiScrewQ (collatzWordScrews w)) * n0 ≤
             collatzWordPEven w * (multiScrewQ (collatzWordScrews w) - collatzWordPOdd w) := by omega
  have hE1 : multiScrewQ (collatzWordScrews w) * (n0 + 1) ≤
             multiScrewP (collatzWordScrews w) * n0 + collatzWordPOdd w := by
    have : (multiScrewP (collatzWordScrews w) * n0 + collatzWordPOdd w) -
           multiScrewQ (collatzWordScrews w) * (n0 + 1) =
           (multiScrewP (collatzWordScrews w) - multiScrewQ (collatzWordScrews w)) * n0 -
           (multiScrewQ (collatzWordScrews w) - collatzWordPOdd w) := by
      simp only [Int.sub_mul, Int.mul_add, Int.mul_one]; omega
    omega
  have hE2 : multiScrewP (collatzWordScrews w) * (n0 + 1) ≤
             multiScrewQ (collatzWordScrews w) * (n0 + collatzWordPEven w) := by
    have : multiScrewQ (collatzWordScrews w) * (n0 + collatzWordPEven w) -
           multiScrewP (collatzWordScrews w) * (n0 + 1) =
           (collatzWordPEven w * multiScrewQ (collatzWordScrews w) - multiScrewP (collatzWordScrews w)) -
           (multiScrewP (collatzWordScrews w) - multiScrewQ (collatzWordScrews w)) * n0 := by
      simp only [Int.mul_add, Int.sub_mul, Int.mul_one,
                 Int.mul_comm (multiScrewQ (collatzWordScrews w)) (collatzWordPEven w)]; omega
    omega
  have hU1 : multiScrewP (collatzWordScrews w) + multiScrewQ (collatzWordScrews w) - 2 * collatzWordPOdd w ≤
             (multiScrewP (collatzWordScrews w) - multiScrewQ (collatzWordScrews w)) * (2 * n0 + 1) := by
    have : (multiScrewP (collatzWordScrews w) - multiScrewQ (collatzWordScrews w)) * (2 * n0 + 1) =
           2 * ((multiScrewP (collatzWordScrews w) - multiScrewQ (collatzWordScrews w)) * n0) +
           (multiScrewP (collatzWordScrews w) - multiScrewQ (collatzWordScrews w)) := by
      simp only [Int.mul_add, Int.add_mul, Int.mul_one, Int.one_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  have hU2 : (multiScrewP (collatzWordScrews w) - multiScrewQ (collatzWordScrews w)) * (2 * n0 + 1) ≤
             (2 * collatzWordPEven w - 1) * multiScrewQ (collatzWordScrews w) - multiScrewP (collatzWordScrews w) := by
    have hL : (multiScrewP (collatzWordScrews w) - multiScrewQ (collatzWordScrews w)) * (2 * n0 + 1) =
              2 * ((multiScrewP (collatzWordScrews w) - multiScrewQ (collatzWordScrews w)) * n0) +
              (multiScrewP (collatzWordScrews w) - multiScrewQ (collatzWordScrews w)) := by
      simp only [Int.mul_add, Int.add_mul, Int.mul_one, Int.one_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    have hR : (2 * collatzWordPEven w - 1) * multiScrewQ (collatzWordScrews w) - multiScrewP (collatzWordScrews w) =
              2 * (collatzWordPEven w * multiScrewQ (collatzWordScrews w)) - multiScrewQ (collatzWordScrews w) -
              multiScrewP (collatzWordScrews w) := by
      simp only [Int.sub_mul, Int.one_mul, Int.mul_assoc]
    omega
  refine ⟨⟨hB1, hB2⟩, ⟨hE1, hE2⟩, ⟨hU1, hU2⟩, ?_,
          by intro hP4 hQ3 hPo2 hPe2 hOdd
             rw [hP4, hQ3, hPo2] at hB1
             rw [hP4, hQ3, hPo2, hPe2] at hB2
             omega⟩
  intro hLt hN0
  have hRw1 : 1 ≤ multiScrewD (collatzWordScrews w) := by omega
  have hQP : multiScrewQ (collatzWordScrews w) < multiScrewP (collatzWordScrews w) := by
    rcases Int.lt_trichotomy (multiScrewQ (collatzWordScrews w)) (multiScrewP (collatzWordScrews w)) with hLtQP | hEqQP | hGtQP
    · exact hLtQP
    · have : (multiScrewP (collatzWordScrews w) - multiScrewQ (collatzWordScrews w)) * n0 = 0 := by
        have hSub0 : multiScrewP (collatzWordScrews w) - multiScrewQ (collatzWordScrews w) = 0 := by omega
        rw [hSub0, Int.zero_mul]
      exact False.elim (Int.lt_irrefl 0 (by omega))
    · have hNonpos : (multiScrewP (collatzWordScrews w) - multiScrewQ (collatzWordScrews w)) * n0 ≤ 0 :=
        Int.mul_nonpos_of_nonpos_of_nonneg (by omega) (by omega)
      exact False.elim (Int.lt_irrefl 0 (by omega))
  exact ⟨hRw1, hQP⟩

/-- Multiplicative upper-envelope factor `U_core(L) = ∏_{(P, Q, p) ∈ L} (Q + p - 1)`
across an arbitrary odd-core macro-stage cascade `L : List (Int × Int × Int)`. -/
def coreStageU : List (Int × Int × Int) → Int
  | [] => 1
  | (_, q, p) :: rest => (q + p - 1) * coreStageU rest

/-- Cumulative forward odd-core drift `D_core(L)` across an arbitrary macro-stage cascade
`L : List (Int × Int × Int)` where each stage `(P, Q, p)` satisfies `P q' = Q q + (p - 1)`. -/
def coreStageD : List (Int × Int × Int) → Int
  | [] => 0
  | (P, _, p) :: rest => multiScrewQ rest * (p - 1) + P * coreStageD rest

theorem coreStageU_append (L1 L2 : List (Int × Int × Int)) :
    coreStageU (L1 ++ L2) = coreStageU L1 * coreStageU L2 := by
  induction L1 with
  | nil => dsimp [coreStageU]; omega
  | cons hd tl ih =>
    rcases hd with ⟨P, q, p⟩
    dsimp [coreStageU]
    rw [ih]
    simp only [Int.mul_assoc]

theorem coreStageD_append (L1 L2 : List (Int × Int × Int)) :
    coreStageD (L1 ++ L2) = multiScrewQ L2 * coreStageD L1 + multiScrewP L1 * coreStageD L2 := by
  induction L1 with
  | nil => dsimp [coreStageD, multiScrewP]; omega
  | cons hd tl ih =>
    rcases hd with ⟨P, q, p⟩
    dsimp [coreStageD, multiScrewP]
    rw [ih, multiScrewQ_append]
    simp only [Int.mul_add, Int.add_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega

/-- **Theorem 32 (Countable Odd-Core Macro-Stage Monoid, Dual-Core Drift Conservation
`D_core(L) + E_core(L) = (U_core(L) - Q_core(L)) q₀`, and Multiplicative Cycle Envelope Gap
across Arbitrary Horizons `L : List (Int × Int × Int)`, `0 Prop premises`)**: -/
theorem thm32_collatz_countable_core_stage_monoid_dual_drift_and_cycle_gap
    (L L1 L2 : List (Int × Int × Int)) (q0 qf : Int) :
    let PL := multiScrewP L
    let QL := multiScrewQ L
    let UL := coreStageU L
    let DL := PL * qf - QL * q0
    let EL := UL * q0 - PL * qf
    (multiScrewP (L1 ++ L2) = multiScrewP L1 * multiScrewP L2 ∧
     multiScrewQ (L1 ++ L2) = multiScrewQ L1 * multiScrewQ L2 ∧
     coreStageU (L1 ++ L2) = coreStageU L1 * coreStageU L2 ∧
     coreStageD (L1 ++ L2) = multiScrewQ L2 * coreStageD L1 + multiScrewP L1 * coreStageD L2) ∧
    (DL + EL = (UL - QL) * q0 ∧
     PL * (q0 - qf) = (PL - QL) * q0 - DL ∧
     PL * (q0 - qf) = (PL - UL) * q0 + EL ∧
     (1 ≤ PL → 1 ≤ q0 → 0 ≤ EL → UL < PL → DL < (PL - QL) * q0 ∧ qf < q0)) ∧
    (qf = q0 →
      (PL - QL) * q0 = DL ∧
      (UL - PL) * q0 = EL ∧
      (UL - PL) * DL = (PL - QL) * EL ∧
      (1 ≤ q0 → 1 ≤ DL → 0 ≤ EL →
        QL < PL ∧ PL ≤ UL ∧ (PL = UL ↔ EL = 0))) := by
  intro PL QL UL DL EL
  have hDual : DL + EL = (UL - QL) * q0 := by
    dsimp [DL, EL, PL, QL, UL]
    have hSub : (coreStageU L - multiScrewQ L) * q0 = coreStageU L * q0 - multiScrewQ L * q0 := by
      simp only [Int.sub_mul]
    omega
  have hFermat1 : PL * (q0 - qf) = (PL - QL) * q0 - DL := by
    dsimp [PL, QL, DL]
    have h1 : multiScrewP L * (q0 - qf) = multiScrewP L * q0 - multiScrewP L * qf := by
      simp only [Int.mul_sub]
    have h2 : (multiScrewP L - multiScrewQ L) * q0 = multiScrewP L * q0 - multiScrewQ L * q0 := by
      simp only [Int.sub_mul]
    omega
  have hFermat2 : PL * (q0 - qf) = (PL - UL) * q0 + EL := by
    dsimp [PL, UL, EL]
    have h1 : multiScrewP L * (q0 - qf) = multiScrewP L * q0 - multiScrewP L * qf := by
      simp only [Int.mul_sub]
    have h2 : (multiScrewP L - coreStageU L) * q0 = multiScrewP L * q0 - coreStageU L * q0 := by
      simp only [Int.sub_mul]
    omega
  refine ⟨⟨multiScrewP_append L1 L2, multiScrewQ_append L1 L2,
           coreStageU_append L1 L2, coreStageD_append L1 L2⟩,
          ⟨hDual, hFermat1, hFermat2, ?_⟩, ?_⟩
  · intro hPL1 hq01 hEL0 hULltPL
    have hPos1 : 1 ≤ (PL - UL) * q0 := by
      have := Int.mul_le_mul (by omega : 1 ≤ PL - UL) hq01 (by omega) (by omega); omega
    have hPosDiff : 1 ≤ PL * (q0 - qf) := by omega
    have hDLlt : DL < (PL - QL) * q0 := by omega
    have hqflt : qf < q0 := by
      rcases Int.lt_trichotomy qf q0 with hLt | hEq | hGt
      · exact hLt
      · have : PL * (q0 - qf) = 0 := by
          have hSub0 : q0 - qf = 0 := by omega
          rw [hSub0, Int.mul_zero]
        exact False.elim (Int.lt_irrefl 0 (by omega))
      · have hNonpos : PL * (q0 - qf) ≤ 0 :=
          Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
        exact False.elim (Int.lt_irrefl 0 (by omega))
    exact ⟨hDLlt, hqflt⟩
  · intro hCyc
    have hCycD : (PL - QL) * q0 = DL := by
      dsimp [PL, QL, DL]
      rw [hCyc]
      simp only [Int.sub_mul]
    have hCycE : (UL - PL) * q0 = EL := by
      dsimp [UL, PL, EL]
      rw [hCyc]
      simp only [Int.sub_mul]
    have hCross : (UL - PL) * DL = (PL - QL) * EL := by
      rw [← hCycD, ← hCycE]
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    refine ⟨hCycD, hCycE, hCross, ?_⟩
    intro hq01 hDL1 hEL0
    have hQLltPL : QL < PL := by
      rcases Int.lt_trichotomy QL PL with hLt | hEq | hGt
      · exact hLt
      · have : (PL - QL) * q0 = 0 := by
          have h0 : PL - QL = 0 := by omega
          rw [h0, Int.zero_mul]
        exact False.elim (Int.lt_irrefl 0 (by omega))
      · have hNonpos : (PL - QL) * q0 ≤ 0 :=
          Int.mul_nonpos_of_nonpos_of_nonneg (by omega) (by omega)
        exact False.elim (Int.lt_irrefl 0 (by omega))
    have hPLleUL : PL ≤ UL := by
      rcases Int.lt_trichotomy UL PL with hLt | hEq | hGt
      · have hNeg : (UL - PL) * q0 < 0 :=
          Int.mul_neg_of_neg_of_pos (by omega) (by omega)
        exact False.elim (Int.lt_irrefl 0 (by omega))
      · omega
      · omega
    refine ⟨hQLltPL, hPLleUL, ?_⟩
    constructor
    · intro hEqPU
      have h0 : UL - PL = 0 := by omega
      rw [← hCycE, h0, Int.zero_mul]
    · intro hE0
      rcases Int.lt_trichotomy PL UL with hLt | hEq | hGt
      · have hPos : 0 < (UL - PL) * q0 :=
          Int.mul_pos (by omega) (by omega)
        exact False.elim (Int.lt_irrefl 0 (by omega))
      · exact hEq
      · omega

/-- **Theorem 33 (Boundary Fixed-Point Reflection `n_∞^{(-)} = -1 ↔ n_∞^{(+)} = 0 ↔ n* = +1`,
Cycle Max-to-Min Ratio Bound `n_max ≤ 2^{A-B} n_min`, Large-`n₀` Descent Threshold,
and `q_min`-Parameterized Envelope Collapse)**:
1. **Boundary Fixed Points of the Extremal Envelope Edges and Reflection Law:**
   - On the pure-odd lower edge (`P_even = 1`, `P_w = P_odd`, `R_w = Q_w - P_odd` with `P_odd < Q_w`),
     the cycle equation `(P_w - Q_w) * n₀ = Q_w - P_odd` has the unique solution `n₀ = -1` (`u(-1) = -1`).
   - On the pure-even upper edge (`Q_w = 1`, `P_odd = 1`, `R_w = 0` with `1 < P_w`),
     the cycle equation `(P_w - 1) * n₀ = 0` has the unique solution `n₀ = 0` (`u(0) = +1`).
   - Reflection of `n_∞^{(-)} = -1` across `n_∞^{(+)} = 0` yields `n* = 2 * 0 - (-1) = +1` (`u(+1) = +3`).
2. **Cycle Max-to-Min Ratio and Span Bound across Cyclic Shifts:**
   For any two elements `n_min, n_max` of a cycle sharing the permutation invariants
   `(P_w, Q_w, P_odd, P_even)` of `w : List Bool` (with `(P_w - Q_w) * n_min = multiScrewD (collatzWordScrews w_min)`
   and `(P_w - Q_w) * n_max = multiScrewD (collatzWordScrews w_max)`):
   - `(P_w - Q_w) * (n_max - n_min) ≤ (P_even - 1) * (Q_w - P_odd)`,
   - whenever `P_odd < Q_w` and `Q_w < P_w`: `n_max ≤ P_even * n_min`.
3. **Large-`n₀` Permutation-Free Descent Threshold:**
   For any word `w : List Bool` and trajectory `P_w * n_f - Q_w * n₀ = R_w`,
   whenever `P_even * (Q_w - P_odd) < (P_w - Q_w) * n₀` and `1 ≤ P_w`, one has `n_f < n₀`.
4. **`q_min`-Parameterized Step Envelope Collapse:**
   For any odd-core step `P * q' = Q * q + (p - 1)` with `q_min ≤ q` and `1 ≤ p`:
   `(q_min * Q + p - 1) * q - q_min * P * q' = (p - 1) * (q - q_min) ≥ 0`,
   with equality `(q_min * Q + p - 1) * q = q_min * P * q'` when `1 < p` iff `q = q_min`. -/
theorem thm33_collatz_boundary_fixed_point_reflection_cycle_ratio_and_qmin_collapse
    (w wMin wMax : List Bool) (n0 nf nMin nMax P Q p q qNext qMin : Int) :
    let Pw := multiScrewP (collatzWordScrews w)
    let Qw := multiScrewQ (collatzWordScrews w)
    let Rw := multiScrewD (collatzWordScrews w)
    let Podd := collatzWordPOdd w
    let Peven := collatzWordPEven w
    ((Podd < Qw → (Podd - Qw) * n0 = Qw - Podd → n0 = -1) ∧
     (1 < Pw → (Pw - 1) * n0 = 0 → n0 = 0) ∧
     (2 * (0 : Int) - (-1 : Int) = 1)) ∧
    (multiScrewP (collatzWordScrews wMin) = Pw →
     multiScrewQ (collatzWordScrews wMin) = Qw →
     collatzWordPOdd wMin = Podd →
     collatzWordPEven wMin = Peven →
     multiScrewP (collatzWordScrews wMax) = Pw →
     multiScrewQ (collatzWordScrews wMax) = Qw →
     collatzWordPOdd wMax = Podd →
     collatzWordPEven wMax = Peven →
     (Pw - Qw) * nMin = multiScrewD (collatzWordScrews wMin) →
     (Pw - Qw) * nMax = multiScrewD (collatzWordScrews wMax) →
      (Pw - Qw) * (nMax - nMin) ≤ (Peven - 1) * (Qw - Podd) ∧
      (Podd < Qw → Qw < Pw → nMax ≤ Peven * nMin)) ∧
    (Pw * nf - Qw * n0 = Rw →
     1 ≤ Pw →
     Peven * (Qw - Podd) < (Pw - Qw) * n0 →
      nf < n0) ∧
    (P * qNext = Q * q + (p - 1) →
     qMin ≤ q →
     1 ≤ p →
      (qMin * Q + p - 1) * q - qMin * P * qNext = (p - 1) * (q - qMin) ∧
      0 ≤ (qMin * Q + p - 1) * q - qMin * P * qNext ∧
      (1 < p → ((qMin * Q + p - 1) * q - qMin * P * qNext = 0 ↔ q = qMin))) := by
  intro Pw Qw Rw Podd Peven
  refine ⟨⟨?_, ?_, by omega⟩, ?_, ?_, ?_⟩
  · intro hLt hEq
    rcases Int.lt_trichotomy n0 (-1) with hLt1 | hEq1 | hGt1
    · have hPos : (Podd - Qw) * (n0 + 1) > 0 :=
        Int.mul_pos_of_neg_of_neg (by omega) (by omega)
      have hExpand : (Podd - Qw) * (n0 + 1) = (Podd - Qw) * n0 - (Qw - Podd) := by
        simp only [Int.mul_add, Int.mul_one]; omega
      exact False.elim (Int.lt_irrefl 0 (by omega))
    · exact hEq1
    · have hNeg : (Podd - Qw) * (n0 + 1) < 0 :=
        Int.mul_neg_of_neg_of_pos (by omega) (by omega)
      have hExpand : (Podd - Qw) * (n0 + 1) = (Podd - Qw) * n0 - (Qw - Podd) := by
        simp only [Int.mul_add, Int.mul_one]; omega
      exact False.elim (Int.lt_irrefl 0 (by omega))
  · intro hGt hEq
    rcases Int.lt_trichotomy n0 0 with hLt0 | hEq0 | hGt0
    · have : (Pw - 1) * n0 < 0 := Int.mul_neg_of_pos_of_neg (by omega) hLt0
      exact False.elim (Int.lt_irrefl 0 (by omega))
    · exact hEq0
    · have : (Pw - 1) * n0 > 0 := Int.mul_pos (by omega) hGt0
      exact False.elim (Int.lt_irrefl 0 (by omega))
  · intro hPmin hQmin hPomin hPemin hPmax hQmax hPomax hPemax hCycMin hCycMax
    have h31Min := (thm31_collatz_binary_gear_word_extremal_drift_envelope_and_cycle_squeeze wMin nMin).2.1
    have h31Max := (thm31_collatz_binary_gear_word_extremal_drift_envelope_and_cycle_squeeze wMax nMax).2.1
    rw [hQmin, hPomin, hPemin, ← hCycMin] at h31Min
    rw [hQmax, hPomax, hPemax, ← hCycMax] at h31Max
    rcases h31Min with ⟨hLowMin, _⟩
    rcases h31Max with ⟨_, hHighMax, _⟩
    have hSpan : (Pw - Qw) * (nMax - nMin) ≤ (Peven - 1) * (Qw - Podd) := by
      have h1 : (Pw - Qw) * (nMax - nMin) = (Pw - Qw) * nMax - (Pw - Qw) * nMin := by
        simp only [Int.mul_sub]
      have h2 : (Peven - 1) * (Qw - Podd) = Peven * (Qw - Podd) - (Qw - Podd) := by
        simp only [Int.sub_mul, Int.one_mul]
      omega
    refine ⟨hSpan, ?_⟩
    intro hPoLtQ hQLtP
    have hStep1 : (Qw - Podd) * ((Pw - Qw) * nMax) ≤
                  (Qw - Podd) * (Peven * (Qw - Podd)) := by
      have hDiff : (Qw - Podd) * (Peven * (Qw - Podd)) - (Qw - Podd) * ((Pw - Qw) * nMax) =
                   (Qw - Podd) * (Peven * (Qw - Podd) - (Pw - Qw) * nMax) := by
        simp only [Int.mul_sub]
      have hNonneg : 0 ≤ (Qw - Podd) * (Peven * (Qw - Podd) - (Pw - Qw) * nMax) :=
        Int.mul_nonneg (by omega) (by omega)
      omega
    have hStep2 : (Peven * (Qw - Podd)) * (Qw - Podd) ≤
                  (Peven * (Qw - Podd)) * ((Pw - Qw) * nMin) := by
      have h31w := (thm31_collatz_binary_gear_word_extremal_drift_envelope_and_cycle_squeeze w n0).1
      have hPePos : 1 ≤ Peven := h31w.2.1
      have hPeQPo : 0 ≤ Peven * (Qw - Podd) := Int.mul_nonneg (by omega) (by omega)
      have hDiff : (Peven * (Qw - Podd)) * ((Pw - Qw) * nMin) -
                   (Peven * (Qw - Podd)) * (Qw - Podd) =
                   (Peven * (Qw - Podd)) * ((Pw - Qw) * nMin - (Qw - Podd)) := by
        simp only [Int.mul_sub]
      have hNonneg : 0 ≤ (Peven * (Qw - Podd)) * ((Pw - Qw) * nMin - (Qw - Podd)) :=
        Int.mul_nonneg hPeQPo (by omega)
      omega
    have hCommMid : (Qw - Podd) * (Peven * (Qw - Podd)) = (Peven * (Qw - Podd)) * (Qw - Podd) := by
      simp only [Int.mul_comm]
    have hCombined : (Qw - Podd) * ((Pw - Qw) * nMax) ≤ (Peven * (Qw - Podd)) * ((Pw - Qw) * nMin) := by
      omega
    have hFactorDiff : 0 ≤ ((Qw - Podd) * (Pw - Qw)) * (Peven * nMin - nMax) := by
      have hId : ((Qw - Podd) * (Pw - Qw)) * (Peven * nMin - nMax) =
                 (Peven * (Qw - Podd)) * ((Pw - Qw) * nMin) - (Qw - Podd) * ((Pw - Qw) * nMax) := by
        calc ((Qw - Podd) * (Pw - Qw)) * (Peven * nMin - nMax)
          _ = ((Qw - Podd) * (Pw - Qw)) * (Peven * nMin) - ((Qw - Podd) * (Pw - Qw)) * nMax := by
            simp only [Int.mul_sub]
          _ = (Peven * (Qw - Podd)) * ((Pw - Qw) * nMin) - (Qw - Podd) * ((Pw - Qw) * nMax) := by
            simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      omega
    have hCoeffPos : 0 < (Qw - Podd) * (Pw - Qw) := Int.mul_pos (by omega) (by omega)
    rcases Int.lt_trichotomy (Peven * nMin - nMax) 0 with hLt | hEq | hGt
    · have hNeg : ((Qw - Podd) * (Pw - Qw)) * (Peven * nMin - nMax) < 0 :=
        Int.mul_neg_of_pos_of_neg hCoeffPos hLt
      exact False.elim (Int.lt_irrefl 0 (by omega))
    · omega
    · omega
  · intro hTraj hPw1 hThresh
    have h31 := (thm31_collatz_binary_gear_word_extremal_drift_envelope_and_cycle_squeeze w n0).2.1
    rcases h31 with ⟨_, hRwHigh, _⟩
    have hRwHigh' : Rw ≤ Peven * (Qw - Podd) := hRwHigh
    have hFermat : Pw * (n0 - nf) = (Pw - Qw) * n0 - Rw := by
      have h1 : Pw * (n0 - nf) = Pw * n0 - Pw * nf := by simp only [Int.mul_sub]
      have h2 : (Pw - Qw) * n0 = Pw * n0 - Qw * n0 := by simp only [Int.sub_mul]
      omega
    have hPos : 0 < Pw * (n0 - nf) := by omega
    rcases Int.lt_trichotomy nf n0 with hLt | hEq | hGt
    · exact hLt
    · have : Pw * (n0 - nf) = 0 := by
        have h0 : n0 - nf = 0 := by omega
        rw [h0, Int.mul_zero]
      exact False.elim (Int.lt_irrefl 0 (by omega))
    · have hNonpos : Pw * (n0 - nf) ≤ 0 :=
        Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
      exact False.elim (Int.lt_irrefl 0 (by omega))
  · intro hStep hqMin hP1
    have hId : (qMin * Q + p - 1) * q - qMin * P * qNext = (p - 1) * (q - qMin) := by
      have hMul : qMin * P * qNext = qMin * (P * qNext) := by simp only [Int.mul_assoc]
      rw [hMul, hStep]
      simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
                 Int.mul_one, Int.one_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      omega
    have hNonneg : 0 ≤ (p - 1) * (q - qMin) := Int.mul_nonneg (by omega) (by omega)
    refine ⟨hId, by omega, ?_⟩
    intro hPgt1
    rw [hId]
    constructor
    · intro hZero
      rcases Int.lt_trichotomy q qMin with hLt | hEq | hGt
      · omega
      · exact hEq
      · have hPos : 0 < (p - 1) * (q - qMin) := Int.mul_pos (by omega) (by omega)
        exact False.elim (Int.lt_irrefl 0 (by omega))
    · intro hEq
      have h0 : q - qMin = 0 := by omega
      rw [h0, Int.mul_zero]

/-- **Theorem 37 (Orbital Shift Derivative across Arbitrary Binary Gear Words `w : List Bool`,
Automatic Parity-DivisibilityPropagation along Cycles, Bilateral `(q_min, q_max)` Extremum Sandwich,
and Resonant Gap `(2^A - 3^B)` Elimination)**:
1. **Orbital Shift Identities for Every Binary Gear Word `rest : List Bool` (Cycle-Free):**
   - Cyclic shift of an even gear `false` (`𝒢_even = (2, 1, 0)`):
     `multiScrewD (collatzWordScrews (false :: rest)) = 2 * multiScrewD (collatzWordScrews (rest ++ [false]))`,
     `multiScrewP (collatzWordScrews (false :: rest)) = multiScrewP (collatzWordScrews (rest ++ [false]))`,
     `multiScrewQ (collatzWordScrews (false :: rest)) = multiScrewQ (collatzWordScrews (rest ++ [false]))`.
   - Cyclic shift of an odd gear `true` (`𝒢_odd = (2, 3, 1)`):
     `2 * multiScrewD (collatzWordScrews (rest ++ [true])) - 3 * multiScrewD (collatzWordScrews (true :: rest)) = multiScrewP (collatzWordScrews (true :: rest)) - multiScrewQ (collatzWordScrews (true :: rest))`.
2. **Automatic Parity and Divisibility Propagation along Cycle Shifts:**
   - For any word starting with `false`, `multiScrewD (collatzWordScrews (false :: rest)) % 2 = 0`,
     and if `(P_w - Q_w) * n₀ = R(false :: rest)` with `n₀ = 2 * n₁`, then `(P_w - Q_w) * n₁ = R(rest ++ [false])`
     (whenever `P_w ≠ Q_w`, i.e., `2` cancels).
   - For any word starting with `true`, `multiScrewQ (collatzWordScrews rest) % 2 = 1` and
     `multiScrewD (collatzWordScrews (true :: rest)) % 2 = 1`, and if `(P_w - Q_w) * n₀ = R(true :: rest)`
     with `2 * n₁ = 3 * n₀ + 1`, then `(P_w - Q_w) * n₁ = R(rest ++ [true])`.
3. **Bilateral `(q_min, q_max)` Extremum Sandwich on Every Odd-Core Step `P q' = Q q + (p - 1)`:**
   Whenever `q_min ≤ q`, `q ≤ q_max`, and `1 ≤ p`:
   - `0 ≤ (q_min * Q + p - 1) * q - q_min * P * q'` (`= (p - 1) * (q - q_min)`),
   - `0 ≤ q_max * P * q' - (q_max * Q + p - 1) * q` (`= (p - 1) * (q_max - q)`),
   - `((q_min * Q + p - 1) * q - q_min * P * q') + (q_max * P * q' - (q_max * Q + p - 1) * q) = (p - 1) * (q_max - q_min)`.
4. **Resonant Gap `(2^A - 3^B)` Elimination at the Cycle Minimum `n_min`:**
   At the minimum element `n_min` of any cycle with word `w_min` (`(P_w - Q_w) * n_min = R(w_min)`),
   the lower bound `Q_w - P_odd ≤ (P_w - Q_w) * n_min` prevents `P_w - Q_w = 2^A - 3^B` from being
   arbitrarily small relative to `(3^B - 2^B) / n_min`, and for any factor `nMinPow ≥ 1` and upper bound
   `M_bound` satisfying `((P_w - Q_w) * n_min) * nMinPow ≤ M_bound`, eliminating `P_w - Q_w` yields
   `(Q_w - P_odd) * nMinPow ≤ M_bound`. -/
theorem thm37_collatz_resonant_gap_elimination_orbital_shift_and_qmin_qmax_sandwich
    (rest wMin : List Bool) (n0 n1 nMin nMinPow Mbound P Q p q qNext qMin qMax : Int) :
    let Qrest := multiScrewQ (collatzWordScrews rest)
    let RfalseL := multiScrewD (collatzWordScrews (false :: rest))
    let RfalseR := multiScrewD (collatzWordScrews (rest ++ [false]))
    let RtrueL  := multiScrewD (collatzWordScrews (true :: rest))
    let RtrueR  := multiScrewD (collatzWordScrews (rest ++ [true]))
    let Ptrue   := multiScrewP (collatzWordScrews (true :: rest))
    let Qtrue   := multiScrewQ (collatzWordScrews (true :: rest))
    let Pfalse  := multiScrewP (collatzWordScrews (false :: rest))
    let Qfalse  := multiScrewQ (collatzWordScrews (false :: rest))
    -- 1. Orbital shift identities across arbitrary binary gear words:
    (RfalseL = 2 * RfalseR ∧
     Pfalse = multiScrewP (collatzWordScrews (rest ++ [false])) ∧
     Qfalse = multiScrewQ (collatzWordScrews (rest ++ [false])) ∧
     2 * RtrueR - 3 * RtrueL = Ptrue - Qtrue) ∧
    -- 2. Automatic parity and divisibility propagation along cycle shifts:
    (RfalseL % 2 = 0 ∧
     Qrest % 2 = 1 ∧
     RtrueL % 2 = 1 ∧
     ((Pfalse - Qfalse) * n0 = RfalseL → n0 = 2 * n1 → (Pfalse - Qfalse) * n1 = RfalseR) ∧
     ((Ptrue - Qtrue) * n0 = RtrueL → 2 * n1 = 3 * n0 + 1 → (Ptrue - Qtrue) * n1 = RtrueR)) ∧
    -- 3. Bilateral (q_min, q_max) extremum sandwich:
    (P * qNext = Q * q + (p - 1) → qMin ≤ q → q ≤ qMax → 1 ≤ p →
      (qMin * Q + p - 1) * q - qMin * P * qNext = (p - 1) * (q - qMin) ∧
      qMax * P * qNext - (qMax * Q + p - 1) * q = (p - 1) * (qMax - q) ∧
      0 ≤ (qMin * Q + p - 1) * q - qMin * P * qNext ∧
      0 ≤ qMax * P * qNext - (qMax * Q + p - 1) * q ∧
      ((qMin * Q + p - 1) * q - qMin * P * qNext) + (qMax * P * qNext - (qMax * Q + p - 1) * q) =
        (p - 1) * (qMax - qMin)) ∧
    -- 4. Resonant gap (2^A - 3^B) elimination at the cycle minimum n_min:
    ((multiScrewP (collatzWordScrews wMin) - multiScrewQ (collatzWordScrews wMin)) * nMin =
       multiScrewD (collatzWordScrews wMin) →
     1 ≤ nMinPow →
     ((multiScrewP (collatzWordScrews wMin) - multiScrewQ (collatzWordScrews wMin)) * nMin) * nMinPow ≤ Mbound →
      multiScrewQ (collatzWordScrews wMin) - collatzWordPOdd wMin ≤
        (multiScrewP (collatzWordScrews wMin) - multiScrewQ (collatzWordScrews wMin)) * nMin ∧
      (multiScrewQ (collatzWordScrews wMin) - collatzWordPOdd wMin) * nMinPow ≤ Mbound) := by
  intro Qrest RfalseL RfalseR RtrueL RtrueR Ptrue Qtrue Pfalse Qfalse
  have hFalseR : RfalseR = multiScrewD (collatzWordScrews rest) := by
    dsimp [RfalseR]
    rw [collatzWordScrews_append, multiScrewD_append]
    dsimp [collatzWordScrews, collatzGearOfBool, multiScrewQ, multiScrewD]
    simp only [Int.one_mul, Int.mul_zero, Int.add_zero]
  have hFalseL : RfalseL = 2 * RfalseR := by
    dsimp [RfalseL, collatzWordScrews, collatzGearOfBool, multiScrewD]
    rw [hFalseR]
    simp only [Int.mul_zero, Int.zero_add]
  have hPfalseEq : Pfalse = multiScrewP (collatzWordScrews (rest ++ [false])) := by
    dsimp [Pfalse]
    rw [collatzWordScrews_append, multiScrewP_append]
    dsimp [collatzWordScrews, collatzGearOfBool, multiScrewP]
    simp only [Int.mul_one, Int.mul_comm]
  have hQfalseEq : Qfalse = multiScrewQ (collatzWordScrews (rest ++ [false])) := by
    dsimp [Qfalse]
    rw [collatzWordScrews_append, multiScrewQ_append]
    dsimp [collatzWordScrews, collatzGearOfBool, multiScrewQ]
    simp only [Int.mul_one, Int.one_mul]
  have hTrueShift : 2 * RtrueR - 3 * RtrueL = Ptrue - Qtrue := by
    dsimp [RtrueR, RtrueL, Ptrue, Qtrue]
    rw [collatzWordScrews_append, multiScrewD_append]
    dsimp [collatzWordScrews, collatzGearOfBool, multiScrewP, multiScrewQ, multiScrewD]
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_one, Int.one_mul, Int.mul_zero, Int.add_zero,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
  have hQodd : ∀ (l : List Bool), multiScrewQ (collatzWordScrews l) % 2 = 1 := by
    intro l
    induction l with
    | nil => dsimp [collatzWordScrews, multiScrewQ]
    | cons b tl ih =>
      cases b <;> dsimp [collatzWordScrews, collatzGearOfBool, multiScrewQ] <;> omega
  have hQrestOdd : Qrest % 2 = 1 := hQodd rest
  have hRfalseEven : RfalseL % 2 = 0 := by rw [hFalseL]; omega
  have hRtrueOdd : RtrueL % 2 = 1 := by
    have : RtrueL = Qrest * 1 + 2 * multiScrewD (collatzWordScrews rest) := rfl
    rw [this]; omega
  refine ⟨⟨hFalseL, hPfalseEq, hQfalseEq, hTrueShift⟩,
          ⟨hRfalseEven, hQrestOdd, hRtrueOdd, ?_, ?_⟩, ?_, ?_⟩
  · intro hCyc0 hn0
    have hAssoc : (Pfalse - Qfalse) * (2 * n1) = 2 * ((Pfalse - Qfalse) * n1) := by
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    rw [hn0, hAssoc, hFalseL] at hCyc0
    omega
  · intro hCyc0 hn1
    have h2 : 2 * ((Ptrue - Qtrue) * n1) = 2 * RtrueR := by
      have hL : 2 * ((Ptrue - Qtrue) * n1) = (Ptrue - Qtrue) * (2 * n1) := by
        simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      have hExpand : (Ptrue - Qtrue) * (3 * n0 + 1) = 3 * ((Ptrue - Qtrue) * n0) + (Ptrue - Qtrue) := by
        simp only [Int.mul_add, Int.add_mul, Int.mul_one, Int.one_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      rw [hL, hn1, hExpand, hCyc0]
      omega
    omega
  · intro hStep hqMin hqMax hP1
    have hIdMin : (qMin * Q + p - 1) * q - qMin * P * qNext = (p - 1) * (q - qMin) := by
      have hMul : qMin * P * qNext = qMin * (P * qNext) := by simp only [Int.mul_assoc]
      rw [hMul, hStep]
      simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
                 Int.mul_one, Int.one_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
    have hIdMax : qMax * P * qNext - (qMax * Q + p - 1) * q = (p - 1) * (qMax - q) := by
      have hMul : qMax * P * qNext = qMax * (P * qNext) := by simp only [Int.mul_assoc]
      rw [hMul, hStep]
      simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
                 Int.mul_one, Int.one_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]; omega
    have hNonnegMin : 0 ≤ (p - 1) * (q - qMin) := Int.mul_nonneg (by omega) (by omega)
    have hNonnegMax : 0 ≤ (p - 1) * (qMax - q) := Int.mul_nonneg (by omega) (by omega)
    have hSumSpan : ((qMin * Q + p - 1) * q - qMin * P * qNext) +
                    (qMax * P * qNext - (qMax * Q + p - 1) * q) =
                    (p - 1) * (qMax - qMin) := by
      rw [hIdMin, hIdMax]
      simp only [Int.mul_sub]; omega
    exact ⟨hIdMin, hIdMax, by omega, by omega, hSumSpan⟩
  · intro hCycMin hPowPos hUpper
    have h31 := (thm31_collatz_binary_gear_word_extremal_drift_envelope_and_cycle_squeeze wMin nMin).2.1
    rcases h31 with ⟨hLow, _, _⟩
    have hLowCyc : multiScrewQ (collatzWordScrews wMin) - collatzWordPOdd wMin ≤
                   (multiScrewP (collatzWordScrews wMin) - multiScrewQ (collatzWordScrews wMin)) * nMin := by
      omega
    have hDiff : ((multiScrewP (collatzWordScrews wMin) - multiScrewQ (collatzWordScrews wMin)) * nMin) * nMinPow -
                 (multiScrewQ (collatzWordScrews wMin) - collatzWordPOdd wMin) * nMinPow =
                 (((multiScrewP (collatzWordScrews wMin) - multiScrewQ (collatzWordScrews wMin)) * nMin) -
                  (multiScrewQ (collatzWordScrews wMin) - collatzWordPOdd wMin)) * nMinPow := by
      simp only [Int.sub_mul]
    have hNonneg : 0 ≤ (((multiScrewP (collatzWordScrews wMin) - multiScrewQ (collatzWordScrews wMin)) * nMin) -
                        (multiScrewQ (collatzWordScrews wMin) - collatzWordPOdd wMin)) * nMinPow :=
      Int.mul_nonneg (by omega) (by omega)
    exact ⟨hLowCyc, by omega⟩

end RotatorCalculusPaper
