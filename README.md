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

Extending the piecewise-linear trigonometric framework studied by Thompson (`arXiv:1205.3814`), where piecewise derivatives lost the classical sine–cosine coupling at the four diamond corners and integral calculus remained open, this work establishes a closed-form trigonometric and integral calculus over the modular integer ring $\mathbb{Z}_{N_{\mathrm{ring}}(d)}$ ($N_{\mathrm{ring}}(d) = 2^{1+2^d}$) and the $12$-vertex cuboctahedron $O_2(d)\subset\{-1,0,+1\}^d$:

1. **Unit-Vector Self-Duality and the Catalan Diophantine Lock (`catalan_lock_iff_d3`):**
   In a $d$-dimensional space with unit basis vectors $\mathbf{e}_1,\dots,\mathbf{e}_d$, equality between the $1+2^d$ intrinsic choice states of a node ($1$ rest state outside the axes plus $2^d$ participation combinations of the $d$ unit vectors) and the $d\times d = d^2$ elementary transition pairs $(\mathbf{e}_i\to\mathbf{e}_j)$ yields the Catalan Diophantine equation
   $$1 + 2^d = d^2 \iff d = 3,$$
   fixing $\mathrm{modBits}(3)=9$, $N_{\mathrm{ring}}(3)=512$, $\Phi_{\mathrm{half}}(3)=256$, $Q_\square(3)=128$, $K_P(3)=64$, and partitioning the $d^2=9$ transition pairs into $d=3$ longitudinal pairs $(\mathbf{e}_i,\mathbf{e}_i)$ and $d(d-1)=6$ off-diagonal rotation pairs $(\mathbf{e}_i,\mathbf{e}_j)$ ($i\ne j$), whose signed combinations $\pm\mathbf{e}_i\pm\mathbf{e}_j$ form the $2d(d-1)=12$ vertices of the cuboctahedron $O_2(3)$.

2. **Theorem 1 (`thm1_constant_wronskian_weierstrass_lift_and_newton_leibniz`) — Discrete Euler Exponential, Euler's Identity $e^{i\pi}+1=0$, Constant Difference Wronskian, and Weierstrass Lift:**
   - The branchless projection pair $\mathcal{E}_d(\varphi) = (\mathcal{C}_d(\varphi), \mathcal{S}_d(\varphi))$ satisfies quarter-turn multiplication by $i$ ($\mathcal{E}_d(\varphi+Q_\square(d)) = (-\mathcal{S}_d(\varphi), \mathcal{C}_d(\varphi))$) and half-turn Euler's identity across all $512$ ring points:
     $$\mathcal{E}_d(\varphi + \Phi_{\mathrm{half}}(d)) + \mathcal{E}_d(\varphi) = (0, 0) \qquad (e^{i\pi} + 1 = 0).$$
   - The one-step difference Wronskian is **identically constant across all 512 points of the ring**, including the four corner vertices:
     $$\mathcal{W}_d(\varphi) := \mathcal{C}_d(\varphi)\mathcal{S}_d(\varphi+1) - \mathcal{S}_d(\varphi)\mathcal{C}_d(\varphi+1) = \langle \mathcal{E}_d(\varphi+Q_\square(d)), \Delta\mathcal{E}_d(\varphi)\rangle \equiv Q_\square(d) = 128.$$
   - The Brahmagupta–Weierstrass lift $(X_d, Y_d, R_d) = (\mathcal{C}_d^2-\mathcal{S}_d^2, 2\mathcal{C}_d\mathcal{S}_d, \mathcal{C}_d^2+\mathcal{S}_d^2)$ satisfies $X_d(\varphi)^2 + Y_d(\varphi)^2 = R_d(\varphi)^2$ without square roots at all $512$ points, and exact discrete Newton–Leibniz antiderivatives hold across the entire ring.

3. **Theorem 2 (`thm2_closed_form_fresnel_jacobi_dirichlet_parseval_bessel_integrals`) — Closed-Form Evaluation of Non-Elementary Integrals:**
   - **Lemniscate Jacobi Elliptic Triad $(\mathrm{sn}_d, \mathrm{cn}_d, \mathrm{dn}_d)$** at the intrinsic cuboctahedron modulus $k^2 = 1/\|e\|_2^2 = 1/(d-1) = 1/2$, with exact complete and incomplete elliptic integrals of the second kind ($\mathcal{E}_{\mathrm{ell}}(3;2,3) = 163\,840$).
   - **Discrete Fresnel Diffraction Integrals:** $\mathcal{C}_{\mathrm{Fresnel}}(3) = \mathcal{S}_{\mathrm{Fresnel}}(3) = 2048$ via exact half-period cancellation of $480$ oscillating quadratic residues and constructive survival of $32$ stationary-phase points at the bisector $\varphi^2 \equiv K_P(3) = 64 \pmod{512}$.
   - **Dirichlet Sine Integral, Parseval Energy Integral, and Zero-Order Bessel Integral:** $\mathrm{Si}_3(128) = \mathrm{Si}_3(256) = 128$, $\sum_{\varphi=0}^{511}\mathcal{C}_3(\varphi)^2 = 2\,796\,288$, $\mathcal{J}_{0,3}(0)=65\,536$, $\mathcal{J}_{0,3}(1)=32\,768$, and exact root $\mathcal{J}_{0,3}(4)=0$.

4. **Theorem 3 (`thm3_continuum_integration_from_cuboctahedron_archimedes_layers`) — Archimedes Equizonal Partition, Continuum Riemann Integral, $\pi(n)$ Rational Brackets, Calculator-Free Rational Trigonometry, and 3D Euler-Angle Rotator:**
   - Projecting the $12$ vertices of $O_2(3)$ onto any coordinate axis $e_x\in\{-1,0,+1\}$ yields the Archimedes equizonal partition $(4, 4, 4)$, which together with the central node of weight $12$ derives the parabolic quadrature weights $(4, 16, 4) = 4\times(1, 4, 1)$ and the exact 3D continuum Riemann integral $\iiint_{[-1,1]^3} F\,\mathrm{d}V$.
   - **Wronskian-Cube Identity for $\pi(n)$:**
     $$\pi_{\mathrm{out}}(n) - \pi_{\mathrm{in}}(n) = \sum_{j=0}^{n/2-1} \frac{W_s(js)^3}{I_s(js)\,R_d(js)\,R_d((j+1)s)} > 0,$$
     contracting by $2^d/\|e\|_2^2 = 4$ at every polygon doubling ($\pi_3(16) = 142/45$, $\pi_3(512) = 3.141592667\dots$).
   - **Calculator-Free Verlet-Parabola Rational Sine (`verletParabolaSineRat`):**
     $$\sin_{\mathrm{rat}}(d;\,p,q) = \frac{d_{\mathrm{in}}(\square)\,p(\|e\|_2^2 q - p)}{d_{\mathrm{out}}(E)(d)\,q^2 - p(\|e\|_2^2 q - p)},$$
     yielding the exact cuboctahedron invariants $(17/97,\, 1/2,\, 12/17,\, 32/37,\, 1)$ at $(10^\circ, 30^\circ, 45^\circ, 60^\circ, 90^\circ)$.
   - **Second-Moment Isotropy & Fourth-Moment Anisotropy Law (`cuboctSecondMoment`, `cuboctFourthMoment`):**
     $$\sum_{e\in O_2(3)} (\mathbf{k}\cdot e)^2 = 8\,|\mathbf{k}|^2, \qquad \sum_{e\in O_2(3)} (\mathbf{k}\cdot e)^4 = 12\,|\mathbf{k}|^4 - 4\sum_{i=1}^3 k_i^4,$$
     together with the root-free 3D Euler-angle rotator $\mathcal{R}_{\mathrm{Euler}}(\varphi_1,\varphi_2,\varphi_3)$ across the $\dim\mathrm{SO}(3) = d(d-1)/2 = 3$ equatorial squares $(xy, xz, yz)$ of the cuboctahedron.

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
