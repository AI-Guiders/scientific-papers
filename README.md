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
- **Self-Contained Lean 4 Formalization (572 lines, 0 external dependencies):** [`RotatorCalculusPaper.lean`](RotatorCalculusPaper.lean)

---

## Main Mathematical Results (Formally Verified in Lean 4)

Extending the piecewise-linear trigonometric framework studied by Thompson (`arXiv:1205.3814`), where piecewise derivatives lost the classical sine–cosine coupling at the four diamond corners and integral calculus remained open, this work establishes a closed-form trigonometric and integral calculus over the modular integer ring `ℤ_{N_ring(d)}` (`N_ring(d) = 2^(1 + 2^d)`) and the 12-vertex cuboctahedron `O₂(d) ⊂ {-1, 0, +1}^d`:

### 1. Unit-Vector Self-Duality and the Catalan Diophantine Lock (`catalan_lock_iff_d3`)

In a `d`-dimensional space with unit basis vectors `e₁, …, e_d`, equality between the `1 + 2^d` intrinsic choice states of a node (`1` rest state outside the axes plus `2^d` participation combinations of the `d` unit vectors) and the `d × d = d²` elementary transition pairs `(e_i → e_j)` yields the Catalan Diophantine equation:

```text
1 + 2^d = d²   <==>   d = 3
```

This uniquely fixes:
- `modBits(3) = 9`, `N_ring(3) = 512`, `Φ_half(3) = 256`, `Q_□(3) = 128`, `K_P(3) = 64`;
- the decomposition of the `d² = 9` unit-vector transition pairs into `d = 3` longitudinal pairs `(e_i, e_i)` and `d(d - 1) = 6` off-diagonal rotation pairs `(e_i, e_j)` (`i ≠ j`), whose signed combinations `±e_i ± e_j` form the `2d(d - 1) = 12` vertices of the cuboctahedron `O₂(3)` of squared Euclidean norm `‖e‖₂² = d - 1 = 2`.

### 2. Theorem 1 (`thm1_constant_wronskian_weierstrass_lift_and_newton_leibniz`) — Discrete Euler Exponential, Euler's Identity `e^(iπ) + 1 = 0`, Constant Difference Wronskian, and Weierstrass Lift

- **Discrete Euler Exponential and Euler's Identity:**  
  The branchless projection pair `E_d(φ) = (C_d(φ), S_d(φ))` satisfies quarter-turn multiplication by `i` (`E_d(φ + Q_□(d)) = (-S_d(φ), C_d(φ))`) and half-turn Euler's identity across all 512 points of the ring:
  ```text
  E_d(φ + Φ_half(d)) + E_d(φ) = (0, 0)      (e^(iπ) + 1 = 0)
  ```
- **Universal Constant Difference Wronskian:**  
  The one-step difference Wronskian is **identically constant across all 512 points of the ring**, including the four corner vertices:
  ```text
  W_d(φ) := C_d(φ) * S_d(φ + 1) - S_d(φ) * C_d(φ + 1)
          = <E_d(φ + Q_□(d)), ΔE_d(φ)>  ≡  Q_□(d) = 128
  ```
- **Brahmagupta–Weierstrass Euclidean Lift & Discrete Newton–Leibniz Theorem:**  
  The polynomial lift `(X_d, Y_d, R_d) = (C_d² - S_d², 2 * C_d * S_d, C_d² + S_d²)` satisfies `X_d(φ)² + Y_d(φ)² = R_d(φ)²` without square roots at all 512 points, and exact discrete Newton–Leibniz antiderivatives hold across the entire ring (`∑_{φ=0}^{255} S₃(φ) = Q_□(3)² = 16,384`).

### 3. Theorem 2 (`thm2_closed_form_fresnel_jacobi_dirichlet_parseval_bessel_integrals`) — Closed-Form Evaluation of Non-Elementary Integrals

- **Lemniscate Jacobi Elliptic Triad `(sn_d, cn_d, dn_d)`:**  
  At the intrinsic cuboctahedron modulus `k² = 1 / ‖e‖₂² = 1 / (d - 1) = 1/2`, the triad satisfies `|sn_d(φ)| + |cn_d(φ)| = Q_□(d)` and `2 * dn_d(φ) + |sn_d(φ)| = Φ_half(d)` across all 512 points, yielding closed-form complete and incomplete elliptic integrals of the second kind (`E_ell(3; 2, 3) = 163,840`).
- **Discrete Fresnel Diffraction Integrals:**  
  `C_Fresnel(3) = S_Fresnel(3) = 2048` via exact half-period cancellation of 480 oscillating quadratic residues and constructive survival of 32 stationary-phase points at the bisector `φ² ≡ K_P(3) = 64 (mod 512)`.
- **Dirichlet Sine Integral, Parseval Energy Integral, and Zero-Order Bessel Integral:**  
  `Si₃(128) = Si₃(256) = 128`, `∑_{φ=0}^{511} C₃(φ)² = 2,796,288`, `J_{0,3}(0) = 65,536`, `J_{0,3}(1) = 32,768`, and the exact root `J_{0,3}(4) = 0`.

### 4. Theorem 3 (`thm3_continuum_integration_from_cuboctahedron_archimedes_layers`) — Archimedes Equizonal Partition, Continuum Riemann Integral, `π(n)` Rational Brackets, Calculator-Free Rational Trigonometry, and 3D Euler-Angle Rotator

- **Archimedes Equizonal Partition & 3D Continuum Riemann Integral:**  
  Projecting the 12 vertices of `O₂(3)` onto any coordinate axis `e_x ∈ {-1, 0, +1}` yields the Archimedes equizonal partition `(4, 4, 4)`, which together with the central node of weight 12 derives Simpson's parabolic weights `(4, 16, 4) = 4 × (1, 4, 1)` and reproduces the exact 3D continuum Riemann integral `∭_{[-1,1]³} F dV`.
- **Wronskian-Cube Identity for `π(n)`:**
  ```text
  π_out(n) - π_in(n) = ∑_{j=0}^{n/2 - 1} W_s(j*s)³ / (I_s(j*s) * R_d(j*s) * R_d((j+1)*s)) > 0
  ```
  contracting by `2^d / ‖e‖₂² = 4` at every polygon doubling (`π₃(16) = 142/45 = 3.1555…`, `π₃(512) = 3.141592667…`, giving 8 exact decimal digits of `π` in pure rationals).
- **Calculator-Free Verlet-Parabola Rational Sine (`verletParabolaSineRat`):**
  ```text
  sin_rat(d; p, q) = (4 * p * (2*q - p)) / (5 * q² - p * (2*q - p))
  ```
  evaluating `sin` and `cos` in two arithmetic operations and returning the exact structural ratios of the cuboctahedron `(17/97, 1/2, 12/17, 32/37, 1)` at `(10°, 30°, 45°, 60°, 90°)`.
- **Second-Moment Isotropy, Fourth-Moment Anisotropy Law, and 3D Euler-Angle Rotator:**
  ```text
  ∑_{e ∈ O₂(3)} (k · e)² = 8 |k|²,       ∑_{e ∈ O₂(3)} (k · e)⁴ = 12 |k|⁴ - 4 ∑_{i=1}^3 k_i⁴
  ```
  together with the root-free 3D Euler-angle rotator `R_Euler(φ₁, φ₂, φ₃)` across the `dim SO(3) = d(d - 1)/2 = 3` equatorial squares `(xy, xz, yz)` of the cuboctahedron, preserving the exact spherical norm `‖R_Euler(φ₁, φ₂, φ₃) v‖₂² = (R_d(φ₁) R_d(φ₂) R_d(φ₃))² ‖v‖₂²`.

---

## Reproducing the Lean 4 Verification

Requires Lean 4 (tested with Lean 4.15+ / 4.36.0; zero external packages or Mathlib required):

```bash
lake build
lake env lean RotatorCalculusPaper.lean
```

Expected `#print axioms` output at the end of `RotatorCalculusPaper.lean`:
```text
'RotatorCalculusPaper.catalan_lock_iff_d3' depends on axioms: [propext, Quot.sound]
'RotatorCalculusPaper.thm1_constant_wronskian_weierstrass_lift_and_newton_leibniz' depends on axioms: [propext, Quot.sound]
'RotatorCalculusPaper.thm2_closed_form_fresnel_jacobi_dirichlet_parseval_bessel_integrals' depends on axioms: [propext, Quot.sound]
'RotatorCalculusPaper.thm3_continuum_integration_from_cuboctahedron_archimedes_layers' depends on axioms: [propext, Quot.sound]
```
(`0 sorryAx`, `0 Classical.choice`).
