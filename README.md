# Cuboctahedral Rotator Calculus in Lean 4

**On a Remarkable Property of the Cuboctahedral Rotator, Euler's Identity, and Closed-Form Evaluation of Fresnel, Jacobi, Bessel, and Dirichlet Integrals in Lean 4**  
*(Об одном замечательном свойстве кусочно-линейного ротатора на кубооктаэдре, тождестве Эйлера и замкнутом вычислении интегралов типа Френеля, Якоби, Бесселя и Дирихле)*

**Author:** Dmitrii A. Karataev (Д. А. Каратаев)  
**Formal Verification Partner:** Luch (Луч)  
**License:** MIT (Lean 4 formalization code) / CC-BY-4.0 (LaTeX manuscripts and PDFs)

---

## Manuscript PDFs & Sources

- **English Preprint (PDF):** [`paper/paper-rotator-calculus-en.pdf`](paper/paper-rotator-calculus-en.pdf) ([LaTeX source](paper/paper-rotator-calculus-en.tex))
- **Russian Preprint (PDF):** [`paper/paper-rotator-calculus-ru.pdf`](paper/paper-rotator-calculus-ru.pdf) ([LaTeX source](paper/paper-rotator-calculus-ru.tex))
- **Self-Contained Lean 4 Formalization (495 lines, 0 external dependencies):** [`RotatorCalculusPaper.lean`](RotatorCalculusPaper.lean)

---

## Main Mathematical Results (Formally Verified in Lean 4)

Extending the piecewise-linear trigonometric framework studied by Thompson (`arXiv:1205.3814`), where piecewise derivatives lost the classical sine–cosine coupling at the four diamond corners and integral calculus remained open, this work establishes a closed-form trigonometric and integral calculus on the 3D Archimedean cuboctahedron `O₂ = {e ∈ {-1, 0, +1}³ | e_x² + e_y² + e_z² = 2}` (`12` vertices, `6` square faces, `8` triangular faces) and the associated discrete phase ring `ℤ_{512}` (quarter-period `Q_□ = 2^(8 - 1) = 128`, half-period `Φ_half = 256`, full period `N_ring = 512`, octant bisector step `K_P = 64`):

### 1. Theorem 1 (`thm1_constant_wronskian_weierstrass_lift_and_newton_leibniz`) — Discrete Euler Exponential, Euler's Identity `e^(iπ) + 1 = 0`, Constant Difference Wronskian, and Weierstrass Lift

- **Discrete Euler Exponential and Euler's Identity:**  
  The branchless projection pair `E₃(φ) = (C₃(φ), S₃(φ))` with `C₃(φ) = Q_□ - |wrap(φ)|` and `S₃(φ) = C₃(φ - Q_□)` satisfies quarter-turn multiplication by `i` (`E₃(φ + Q_□) = (-S₃(φ), C₃(φ))`) and half-turn Euler's identity across all 512 points of the ring:
  ```text
  E₃(φ + Φ_half) + E₃(φ) = (0, 0)      (e^(iπ) + 1 = 0)
  ```
- **Universal Constant Difference Wronskian:**  
  The one-step difference Wronskian is **identically constant across all 512 points of the ring**, including the four corner vertices:
  ```text
  W₃(φ) := C₃(φ) * S₃(φ + 1) - S₃(φ) * C₃(φ + 1)
          = <E₃(φ + Q_□), ΔE₃(φ)>  ≡  Q_□ = 128
  ```
- **Brahmagupta–Weierstrass Euclidean Lift & Discrete Newton–Leibniz Theorem:**  
  The polynomial lift `(X₃, Y₃, R₃) = (C₃² - S₃², 2 * C₃ * S₃, C₃² + S₃²)` satisfies `X₃(φ)² + Y₃(φ)² = R₃(φ)²` without square roots at all 512 points, and exact discrete Newton–Leibniz antiderivatives hold across the entire ring (`∑_{φ=0}^{255} S₃(φ) = Q_□² = 16,384`).

### 2. Theorem 2 (`thm2_closed_form_fresnel_jacobi_dirichlet_parseval_bessel_integrals`) — Closed-Form Evaluation of Non-Elementary Integrals

- **Lemniscate Jacobi Elliptic Triad `(sn₃, cn₃, dn₃)`:**  
  At the intrinsic cuboctahedron modulus `k² = 1 / ‖e‖₂² = 1/2`, the triad satisfies `|sn₃(φ)| + |cn₃(φ)| = Q_□` and `2 * dn₃(φ) + |sn₃(φ)| = Φ_half` across all 512 points, yielding closed-form complete and incomplete elliptic integrals of the second kind (`E_ell(3; 2, 3) = 163,840`).
- **Discrete Fresnel Diffraction Integrals:**  
  `C_Fresnel(3) = S_Fresnel(3) = 2048` via exact half-period cancellation of 480 oscillating quadratic residues and constructive survival of 32 stationary-phase points at the bisector `φ² ≡ K_P = 64 (mod 512)`.
- **Dirichlet Sine Integral, Parseval Energy Integral, and Zero-Order Bessel Integral:**  
  `Si₃(128) = Si₃(256) = 128`, `∑_{φ=0}^{511} C₃(φ)² = 2,796,288`, `J_{0,3}(0) = 65,536`, `J_{0,3}(1) = 32,768`, and the exact root `J_{0,3}(4) = 0`.

### 3. Theorem 3 (`thm3_continuum_integration_from_cuboctahedron_archimedes_layers`) — Archimedes Equizonal Partition, Continuum Riemann Integral, `π(n)` Rational Brackets, Calculator-Free Rational Trigonometry, and 3D Euler-Angle Rotator

- **Archimedes Equizonal Partition & 3D Continuum Riemann Integral:**  
  Projecting the 12 vertices of `O₂` onto any coordinate axis `e_x ∈ {-1, 0, +1}` yields the Archimedes equizonal partition `(4, 4, 4)`, which together with the central node of weight 12 derives Simpson's parabolic weights `(4, 16, 4) = 4 × (1, 4, 1)` and reproduces the exact 3D continuum Riemann integral `∭_{[-1,1]³} F dV`.
- **Wronskian-Cube Identity for `π(n)`:**
  ```text
  π_out(n) - π_in(n) = ∑_{j=0}^{n/2 - 1} W_s(j*s)³ / (I_s(j*s) * R₃(j*s) * R₃((j+1)*s)) > 0
  ```
  contracting by `4` at every polygon doubling (`π₃(16) = 142/45 = 3.1555…`, `π₃(512) = 3.141592667…`, giving 8 exact decimal digits of `π` in pure rationals).
- **Calculator-Free Verlet-Parabola Rational Sine (`verletParabolaSineRat`):**
  ```text
  sin_rat(p, q) = (4 * p * (2*q - p)) / (5 * q² - p * (2*q - p))
  ```
  evaluating `sin` and `cos` in two arithmetic operations and returning the exact structural ratios of the cuboctahedron `(17/97, 1/2, 12/17, 32/37, 1)` at `(10°, 30°, 45°, 60°, 90°)`.
- **Second-Moment Isotropy, Fourth-Moment Anisotropy Law, and 3D Euler-Angle Rotator:**
  ```text
  ∑_{e ∈ O₂} (k · e)² = 8 |k|²,       ∑_{e ∈ O₂} (k · e)⁴ = 12 |k|⁴ - 4 ∑_{i=1}^3 k_i⁴
  ```
  together with the root-free 3D Euler-angle rotator `R_Euler(φ₁, φ₂, φ₃)` across the `dim SO(3) = 3` equatorial squares `(xy, xz, yz)` of the cuboctahedron, preserving the exact spherical norm `‖R_Euler(φ₁, φ₂, φ₃) v‖₂² = (R₃(φ₁) R₃(φ₂) R₃(φ₃))² ‖v‖₂²`.

### 4. Theorem 4 (`thm4_boolean_post_completeness_3sat_reduction_and_channel_orthogonality`) — Post Functional Completeness `{NOT, XOR, OR, AND}`, Branchless 3-SAT Representation, `7 → 1` Remainder Gluing, and Two-Channel Non-Commutativity on `ℤ_{512}`

On the antipodal poles `{0, Φ_half} = {0, 256} ⊂ ℤ_{512}` (`C₃(0) = +128` encoding `True`, `C₃(256) = -128` encoding `False`), the rotator induces two canonical algebraic channels on triangular faces `(ψ₁, ψ₂, ψ₃) ∈ {0, 256}³`:
- **Channel 1 (Post's affine linear class `L` — pre-rotator phase addition):**  
  `NOT(ψ) = (ψ + 256) mod 512` (`C₃(ψ + 256) = -C₃(ψ)`) and 3-input `XOR` via `Q_□² * C₃(ψ₁ + ψ₂ + ψ₃) = C₃(ψ₁) * C₃(ψ₂) * C₃(ψ₃)`, with `256 + 256 ≡ 0 (mod 512)`.
- **Channel 2 (Non-linear threshold class — post-rotator projection sum with integer division by `512`):**
  ```text
  q_OR(ψ₁, ψ₂, ψ₃)  = tdiv(128 - (C₃(ψ₁) + C₃(ψ₂) + C₃(ψ₃)), 512) ∈ {0, 1}
  q_AND(ψ₁, ψ₂, ψ₃) = tdiv(128 + (C₃(ψ₁) + C₃(ψ₂) + C₃(ψ₃)), 512) ∈ {0, 1}
  ```
  By Turing–CA polynomial equivalence (`P_TM ≡ P_CA`, Cook–Levin), every Boolean circuit decomposes into Channel 1 and Channel 2, and a 3-SAT formula of `M` clauses is satisfiable iff `∑_{m=1}^M q_OR(ψ_{m,1}, ψ_{m,2}, ψ_{m,3}) = 0`.
- **Three Verified Algebraic Asymmetries Between Forward Verification (`NP`) and Inversion (`P`):**
  1. **Non-injective `7 → 1` remainder gluing:** `q_OR` discards the 3-valued remainder `r ∈ {-256, 0, +256}` and maps `7` distinct satisfying octants onto `q_OR = 0` (`1 → 7` preimage branching per clause).
  2. **Identical annihilation of Channel 2 linear gradients on Channel 1 parity constraints:** across the `4` clauses encoding a `3-XOR` parity equation, the sum of linear projections `C₃` vanishes identically on all `8` octants (`xor4LinearGradientSum ≡ 0`).
  3. **Non-distributivity and non-commutativity of Channel 1 and Channel 2:** `C₃(0 + 0) = 128 ≠ 256 = C₃(0) + C₃(0)` and `q_AND(0 + 0, 0, 0) = 1 ≠ 0 = (q_AND(0, 0, 0) + q_AND(0, 0, 0)) mod 2`.

---

## Reproducing the Lean 4 Verification

Requires Lean 4 (tested with Lean 4.15+ / 4.36.0; zero external packages or Mathlib required):

```bash
lake build
lake env lean RotatorCalculusPaper.lean
```

Expected `#print axioms` output at the end of `RotatorCalculusPaper.lean`:
```text
'RotatorCalculusPaper.thm1_constant_wronskian_weierstrass_lift_and_newton_leibniz' depends on axioms: [propext]
'RotatorCalculusPaper.thm2_closed_form_fresnel_jacobi_dirichlet_parseval_bessel_integrals' depends on axioms: [propext]
'RotatorCalculusPaper.thm3_continuum_integration_from_cuboctahedron_archimedes_layers' depends on axioms: [propext]
'RotatorCalculusPaper.thm4_boolean_post_completeness_3sat_reduction_and_channel_orthogonality' depends on axioms: [propext]
```
(`0 sorryAx`, `0 Classical.choice`).
