import Kepler.ConservedQuantities
import Kepler.MomentMap
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option linter.style.longLine false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.style.setOption false
set_option linter.flexible false

namespace Kepler

noncomputable section

lemma inner_cross_perm (u v w : Vec3) :
    inner ℝ (cross u v) w = inner ℝ v (cross w u) := by
  simp [inner_fin3, cross, cross_apply]
  ring

lemma inner_smul_inv_radial (μ : Real) (q : Vec3) :
    inner ℝ ((μ / radialDist q) • q) q = μ * radialDist q := by
  by_cases hq : radialDist q = 0
  · simp [hq]
  · rw [real_inner_smul_left, real_inner_self_eq_norm_sq, radialDist]
    field_simp [hq]

lemma cross_smul_right (a : Real) (u v : Vec3) :
    cross u (a • v) = a • cross u v := by
  ext i
  fin_cases i <;> simp [cross, cross_apply]
  · ring
  · ring
  · ring

lemma cross_add_left (u v w : Vec3) :
    cross (u + v) w = cross u w + cross v w := by
  ext i
  fin_cases i <;> simp [cross, cross_apply]
  · ring
  · ring
  · ring

lemma cross_add_right (u v w : Vec3) :
    cross u (v + w) = cross u v + cross u w := by
  ext i
  fin_cases i <;> simp [cross, cross_apply]
  · ring
  · ring
  · ring

lemma cross_sub_right (u v w : Vec3) :
    cross u (v - w) = cross u v - cross u w := by
  ext i
  fin_cases i <;> simp [cross, cross_apply]
  · ring
  · ring
  · ring

lemma cross_cross_eq_inner (u v w : Vec3) :
    cross u (cross v w) = (inner ℝ u w) • v - (inner ℝ v u) • w := by
  ext i
  fin_cases i <;> simp [cross, cross_apply, inner_fin3]
  · ring
  · ring
  · ring

lemma inner_cross_left_zero (u v : Vec3) :
    inner ℝ u (cross u v) = 0 := by
  simp [inner_fin3, cross, cross_apply]
  ring

lemma inner_cross_right_zero (u v : Vec3) :
    inner ℝ v (cross u v) = 0 := by
  simp [inner_fin3, cross, cross_apply]
  ring

lemma norm_cross_sq (u v : Vec3) :
    ‖cross u v‖ ^ (2 : Nat) =
      ‖u‖ ^ (2 : Nat) * ‖v‖ ^ (2 : Nat) - (inner ℝ u v) ^ (2 : Nat) := by
  have hdot (a b : Vec3) : (fun i => a i) ⬝ᵥ (fun i => b i) = inner ℝ a b := by
    rw [inner_fin3]
    simp [dotProduct, Fin.sum_univ_three, add_assoc]
  calc
    ‖cross u v‖ ^ (2 : Nat) = inner ℝ (cross u v) (cross u v) := by
      rw [real_inner_self_eq_norm_sq]
    _ = inner ℝ u u * inner ℝ v v - inner ℝ u v * inner ℝ v u := by
      rw [← hdot (cross u v) (cross u v), ← hdot u u, ← hdot v v, ← hdot u v, ← hdot v u]
      simpa [cross] using
        (cross_dot_cross (fun i => u i) (fun i => v i) (fun i => u i) (fun i => v i))
    _ = ‖u‖ ^ (2 : Nat) * ‖v‖ ^ (2 : Nat) - (inner ℝ u v) ^ (2 : Nat) := by
      rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_comm]
      ring

lemma momentum_from_position_angularMomentum_laplaceLenz
    (mp : MassParam) (gp : GravitationalParam) (z : PhaseSpace)
    (hL : angularMomentum z ≠ 0) :
    z.2 =
      (1 / ‖angularMomentum z‖ ^ (2 : Nat)) •
        cross (angularMomentum z)
          (laplaceLenz mp gp z + ((mp.m * gp.mu) / radialDist z.1) • z.1) := by
  set q : Vec3 := z.1
  set p : Vec3 := z.2
  set L : Vec3 := angularMomentum z
  have hLp : inner ℝ p L = 0 := by
    simpa [q, p, L, angularMomentum] using inner_cross_right_zero q p
  have hcross :
      cross L (cross p L) = ‖L‖ ^ (2 : Nat) • p := by
    calc
      cross L (cross p L)
          = (inner ℝ L L) • p - (inner ℝ p L) • L := by
              simpa [real_inner_comm] using cross_cross_eq_inner L p L
      _ = ‖L‖ ^ (2 : Nat) • p := by
            rw [real_inner_self_eq_norm_sq, hLp]
            simp
  have hsum :
      laplaceLenz mp gp z + ((mp.m * gp.mu) / radialDist q) • q = cross p L := by
    simp [laplaceLenz, radialDist, q, p, L, angularMomentum, sub_eq_add_neg, add_assoc]
  have hnormsq : ‖L‖ ^ (2 : Nat) ≠ 0 := by
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (by simpa [L] using hL))
  calc
    p = (1 : Real) • p := by simp
    _ = ((1 / ‖L‖ ^ (2 : Nat)) * ‖L‖ ^ (2 : Nat)) • p := by
          congr 1
          field_simp [hnormsq]
    _ = (1 / ‖L‖ ^ (2 : Nat)) • (‖L‖ ^ (2 : Nat) • p) := by rw [smul_smul]
    _ = (1 / ‖L‖ ^ (2 : Nat)) • cross L (cross p L) := by rw [hcross]
    _ =
        (1 / ‖L‖ ^ (2 : Nat)) •
          cross L (laplaceLenz mp gp z + ((mp.m * gp.mu) / radialDist q) • q) := by
            rw [hsum]
    _ =
        (1 / ‖L‖ ^ (2 : Nat)) •
          cross (angularMomentum z)
            (laplaceLenz mp gp z + ((mp.m * gp.mu) / radialDist z.1) • z.1) := by
              simp [q, L]

lemma phase_eq_of_position_eq
    (mp : MassParam) (gp : GravitationalParam) (gamma : Real -> PhaseSpace)
    (hgamma : IsSolution mp gp gamma) (hL : angularMomentum (gamma 0) ≠ 0)
    {t1 t2 : Real} (hq : (gamma t1).1 = (gamma t2).1) :
    gamma t1 = gamma t2 := by
  apply Prod.ext hq
  have hLt1 : angularMomentum (gamma t1) ≠ 0 := by
    rw [angularMomentum_const hgamma t1]
    exact hL
  have hLt2 : angularMomentum (gamma t2) ≠ 0 := by
    rw [angularMomentum_const hgamma t2]
    exact hL
  calc
    (gamma t1).2 =
        (1 / ‖angularMomentum (gamma t1)‖ ^ (2 : Nat)) •
          cross (angularMomentum (gamma t1))
            (laplaceLenz mp gp (gamma t1) +
              ((mp.m * gp.mu) / radialDist ((gamma t1).1)) • (gamma t1).1) := by
                simpa using
                  momentum_from_position_angularMomentum_laplaceLenz mp gp (gamma t1) hLt1
    _ =
        (1 / ‖angularMomentum (gamma t2)‖ ^ (2 : Nat)) •
          cross (angularMomentum (gamma t2))
            (laplaceLenz mp gp (gamma t2) +
              ((mp.m * gp.mu) / radialDist ((gamma t2).1)) • (gamma t2).1) := by
                rw [angularMomentum_const hgamma t1, angularMomentum_const hgamma t2,
                  laplaceLenz_const hgamma t1, laplaceLenz_const hgamma t2, hq]
    _ = (gamma t2).2 := by
          simpa using
            (momentum_from_position_angularMomentum_laplaceLenz mp gp (gamma t2) hLt2).symm

lemma ellipse_poly1
    (a b e l x y : Real)
    (hcurve :
      x ^ (2 : Nat) + y ^ (2 : Nat) =
        l ^ (2 : Nat) - 2 * l * e * x + e ^ (2 : Nat) * x ^ (2 : Nat))
    (hl : l = a * (1 - e ^ (2 : Nat)))
    (hb : b ^ (2 : Nat) = a * l) :
    b ^ (2 : Nat) * x ^ (2 : Nat) +
        2 * a * e * b ^ (2 : Nat) * x +
        a ^ (2 : Nat) * y ^ (2 : Nat) =
      b ^ (2 : Nat) * b ^ (2 : Nat) := by
  rw [hl] at hcurve
  rw [hb, hl]
  nlinarith

lemma ellipse_poly2
    (a b e x y : Real)
    (hpoly1 :
      b ^ (2 : Nat) * x ^ (2 : Nat) +
          2 * a * e * b ^ (2 : Nat) * x +
          a ^ (2 : Nat) * y ^ (2 : Nat) =
        b ^ (2 : Nat) * b ^ (2 : Nat))
    (hfocus : a ^ (2 : Nat) - b ^ (2 : Nat) = (a * e) ^ (2 : Nat)) :
    b ^ (2 : Nat) * (x + a * e) ^ (2 : Nat) + a ^ (2 : Nat) * y ^ (2 : Nat) =
      a ^ (2 : Nat) * b ^ (2 : Nat) := by
  nlinarith [hpoly1, hfocus]

lemma ellipse_cartesian_from_poly
    (a b e x y : Real)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hpoly :
      b ^ (2 : Nat) * (x + a * e) ^ (2 : Nat) + a ^ (2 : Nat) * y ^ (2 : Nat) =
        a ^ (2 : Nat) * b ^ (2 : Nat)) :
    ((x + a * e) ^ (2 : Nat)) / (a ^ (2 : Nat)) +
        (y ^ (2 : Nat)) / (b ^ (2 : Nat)) =
      1 := by
  have hden : a ^ (2 : Nat) * b ^ (2 : Nat) ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero 2 ha) (pow_ne_zero 2 hb)
  have hcart_mul :
      ((((x + a * e) ^ (2 : Nat)) / (a ^ (2 : Nat)) +
            (y ^ (2 : Nat)) / (b ^ (2 : Nat))) *
          (a ^ (2 : Nat) * b ^ (2 : Nat))) =
        1 * (a ^ (2 : Nat) * b ^ (2 : Nat)) := by
    calc
      ((((x + a * e) ^ (2 : Nat)) / (a ^ (2 : Nat)) +
            (y ^ (2 : Nat)) / (b ^ (2 : Nat))) *
          (a ^ (2 : Nat) * b ^ (2 : Nat)))
          = b ^ (2 : Nat) * (x + a * e) ^ (2 : Nat) +
              a ^ (2 : Nat) * y ^ (2 : Nat) := by
                field_simp [ha, hb]
      _ = a ^ (2 : Nat) * b ^ (2 : Nat) := hpoly
      _ = 1 * (a ^ (2 : Nat) * b ^ (2 : Nat)) := by ring
  exact mul_right_cancel₀ hden hcart_mul

lemma kepler_first_law_pointwise
    (mp : MassParam) (gp : GravitationalParam) (gamma : Real -> PhaseSpace)
    (_hgamma : IsSolution mp gp gamma) (t : Real) :
    inner ℝ (laplaceLenz mp gp (gamma t)) (gamma t).1 =
      ‖angularMomentum (gamma t)‖ ^ (2 : Nat) - (mp.m * gp.mu) * radialDist ((gamma t).1) := by
  set q : Vec3 := (gamma t).1
  set p : Vec3 := (gamma t).2
  set L : Vec3 := angularMomentum (gamma t)
  have hL : L = cross q p := by
    simp [L, q, p, angularMomentum]
  calc
    inner ℝ (laplaceLenz mp gp (gamma t)) q
        = inner ℝ (cross p L - ((mp.m * gp.mu) / radialDist q) • q) q := by
          simp [laplaceLenz, radialDist, L, q, p, angularMomentum]
    _ = inner ℝ (cross p L) q - inner ℝ (((mp.m * gp.mu) / radialDist q) • q) q := by
          rw [inner_sub_left]
    _ = inner ℝ L (cross q p) - inner ℝ (((mp.m * gp.mu) / radialDist q) • q) q := by
          rw [inner_cross_perm]
    _ = inner ℝ L L - inner ℝ (((mp.m * gp.mu) / radialDist q) • q) q := by
          simp [hL]
    _ = ‖L‖ ^ (2 : Nat) - (mp.m * gp.mu) * radialDist q := by
          simp [inner_smul_inv_radial]

theorem kepler_first_law
    (mp : MassParam) (gp : GravitationalParam) (gamma : Real -> PhaseSpace) (hgamma : IsSolution mp gp gamma) :
    ∀ t : Real,
      let A0 := laplaceLenz mp gp (gamma 0)
      let L0 := angularMomentum (gamma 0)
      let q := (gamma t).1
      inner ℝ A0 q = ‖L0‖ ^ (2 : Nat) - (mp.m * gp.mu) * radialDist q ∧
        (∀ _hq : radialDist q ≠ 0,
          let u := (1 / radialDist q) • q
          ∀ _hden : mp.m * gp.mu + inner ℝ A0 u ≠ 0,
            radialDist q = ‖L0‖ ^ (2 : Nat) / (mp.m * gp.mu + inner ℝ A0 u)) := by
  intro t
  dsimp
  have hcoeff :
      inner ℝ (laplaceLenz mp gp (gamma 0)) (gamma t).1 =
        ‖angularMomentum (gamma 0)‖ ^ (2 : Nat) - (mp.m * gp.mu) * radialDist ((gamma t).1) := by
    have hpt := kepler_first_law_pointwise mp gp gamma hgamma t
    have hA := laplaceLenz_const hgamma t
    have hL := angularMomentum_const hgamma t
    simpa [hA, hL] using hpt
  constructor
  · simpa using hcoeff
  · intro hq hden
    set A0 : Vec3 := laplaceLenz mp gp (gamma 0)
    set L0 : Vec3 := angularMomentum (gamma 0)
    set q : Vec3 := (gamma t).1
    let u : Vec3 := (1 / radialDist q) • q
    have hcoeff0 : inner ℝ A0 q = ‖L0‖ ^ (2 : Nat) - (mp.m * gp.mu) * radialDist q := by
      simpa [A0, L0, q] using hcoeff
    have hqeq : radialDist q • u = q := by
      dsimp [u]
      calc
        radialDist q • ((1 / radialDist q) • q)
            = (radialDist q * (1 / radialDist q)) • q := by rw [smul_smul]
        _ = (1 : Real) • q := by
              congr 1
              field_simp [hq]
        _ = q := by simp
    have hinner : inner ℝ A0 q = radialDist q * inner ℝ A0 u := by
      calc
        inner ℝ A0 q = inner ℝ A0 (radialDist q • u) := by rw [hqeq]
        _ = radialDist q * inner ℝ A0 u := by rw [real_inner_smul_right]
    have hcoeff1 : radialDist q * inner ℝ A0 u = ‖L0‖ ^ (2 : Nat) - (mp.m * gp.mu) * radialDist q := by
      simpa [hinner] using hcoeff0
    have hmul : radialDist q * (mp.m * gp.mu + inner ℝ A0 u) = ‖L0‖ ^ (2 : Nat) := by
      calc
        radialDist q * (mp.m * gp.mu + inner ℝ A0 u)
            = (mp.m * gp.mu) * radialDist q + radialDist q * inner ℝ A0 u := by ring
        _ = (mp.m * gp.mu) * radialDist q + (‖L0‖ ^ (2 : Nat) - (mp.m * gp.mu) * radialDist q) := by
              rw [hcoeff1]
        _ = ‖L0‖ ^ (2 : Nat) := by ring
    exact (eq_div_iff hden).2 (by simpa [u] using hmul)

theorem kepler_first_law_orbit_equation
    (mp : MassParam) (gp : GravitationalParam) (gamma : Real -> PhaseSpace) (hgamma : IsSolution mp gp gamma) :
    ∀ t : Real,
      let A0 := laplaceLenz mp gp (gamma 0)
      let L0 := angularMomentum (gamma 0)
      let q := (gamma t).1
      let r := radialDist q
      let u := (1 / r) • q
      let l := ‖L0‖ ^ (2 : Nat) / (mp.m * gp.mu)
      ∀ _hq : r ≠ 0,
      ∀ _hden : mp.m * gp.mu + inner ℝ A0 u ≠ 0,
        r = ‖L0‖ ^ (2 : Nat) / (mp.m * gp.mu + inner ℝ A0 u) ∧
          (∀ _hA0 : A0 ≠ 0,
            let e := ‖A0‖ / (mp.m * gp.mu)
            r = l / (1 + e * inner ℝ u ((1 / ‖A0‖) • A0))) := by
  intro t
  dsimp
  have hkepler := kepler_first_law mp gp gamma hgamma t
  intro hq hden
  constructor
  · exact hkepler.2 hq hden
  · intro hA0
    set A0 : Vec3 := laplaceLenz mp gp (gamma 0)
    set L0 : Vec3 := angularMomentum (gamma 0)
    set q : Vec3 := (gamma t).1
    let r := radialDist q
    let u := (1 / r) • q
    let e := ‖A0‖ / (mp.m * gp.mu)
    have hcoeff0 : r = ‖L0‖ ^ (2 : Nat) / (mp.m * gp.mu + inner ℝ A0 u) := by
      simpa [A0, L0, q, r, u] using hkepler.2 hq hden
    have hA0norm : ‖A0‖ ≠ 0 := by
      exact norm_ne_zero_iff.mpr hA0
    have hinner : inner ℝ u ((1 / ‖A0‖) • A0) = inner ℝ A0 u / ‖A0‖ := by
      calc
        inner ℝ u ((1 / ‖A0‖) • A0) = (1 / ‖A0‖) * inner ℝ u A0 := by
          rw [real_inner_smul_right]
        _ = (1 / ‖A0‖) * inner ℝ A0 u := by rw [real_inner_comm]
        _ = inner ℝ A0 u / ‖A0‖ := by
          simp [div_eq_mul_inv, mul_comm]
    have hmμ : mp.m * gp.mu ≠ 0 := by
      exact mul_ne_zero (ne_of_gt mp.hm) (ne_of_gt gp.hmu)
    have hscale :
        (mp.m * gp.mu) * (e * inner ℝ u ((1 / ‖A0‖) • A0)) = inner ℝ A0 u := by
      rw [hinner]
      dsimp [e]
      field_simp [ne_of_gt mp.hm, ne_of_gt gp.hmu, hA0norm]
    have hdenom :
        mp.m * gp.mu + inner ℝ A0 u =
          (mp.m * gp.mu) * (1 + e * inner ℝ u ((1 / ‖A0‖) • A0)) := by
      calc
        mp.m * gp.mu + inner ℝ A0 u
            = mp.m * gp.mu + (mp.m * gp.mu) * (e * inner ℝ u ((1 / ‖A0‖) • A0)) := by
                rw [hscale]
        _ = (mp.m * gp.mu) * (1 + e * inner ℝ u ((1 / ‖A0‖) • A0)) := by ring
    have hcoeff1 :
        r = (‖L0‖ ^ (2 : Nat) / (mp.m * gp.mu)) /
          (1 + e * inner ℝ u ((1 / ‖A0‖) • A0)) := by
      calc
        r = ‖L0‖ ^ (2 : Nat) / (mp.m * gp.mu + inner ℝ A0 u) := by rw [hcoeff0]
        _ = ‖L0‖ ^ (2 : Nat) / ((mp.m * gp.mu) * (1 + e * inner ℝ u ((1 / ‖A0‖) • A0))) := by
              rw [hdenom]
        _ = (‖L0‖ ^ (2 : Nat) / (mp.m * gp.mu)) / (1 + e * inner ℝ u ((1 / ‖A0‖) • A0)) := by
              field_simp [ne_of_gt mp.hm, ne_of_gt gp.hmu]
    exact hcoeff1

def eccentricity (mp : MassParam) (gp : GravitationalParam) (z : PhaseSpace) : Real :=
  ‖laplaceLenz mp gp z‖ / (mp.m * gp.mu)

def semiLatusRectum (mp : MassParam) (gp : GravitationalParam) (z : PhaseSpace) : Real :=
  ‖angularMomentum z‖ ^ (2 : Nat) / (mp.m * gp.mu)

theorem orbit_circle_of_zero_laplaceLenz
    (mp : MassParam) (gp : GravitationalParam)
    (gamma : Real -> PhaseSpace) (hgamma : IsSolution mp gp gamma)
    (hA0 : laplaceLenz mp gp (gamma 0) = 0) :
    ∀ t : Real, radialDist (gamma t).1 = semiLatusRectum mp gp (gamma 0) := by
  intro t
  have hcoeff := (kepler_first_law mp gp gamma hgamma t).1
  have hmμ : mp.m * gp.mu ≠ 0 := mul_ne_zero (ne_of_gt mp.hm) (ne_of_gt gp.hmu)
  apply (eq_div_iff hmμ).2
  have hmul :
      (mp.m * gp.mu) * radialDist ((gamma t).1) =
        ‖angularMomentum (gamma 0)‖ ^ (2 : Nat) := by
    have hzero :
        0 =
          ‖angularMomentum (gamma 0)‖ ^ (2 : Nat) -
            (mp.m * gp.mu) * radialDist ((gamma t).1) := by
      simpa [hA0] using hcoeff
    nlinarith
  simpa [semiLatusRectum, mul_comm] using hmul

def semiMajorAxis (mp : MassParam) (gp : GravitationalParam) (z : PhaseSpace) : Real :=
  -(gp.mu / (2 * energy mp gp z))

def semiMinorAxis (mp : MassParam) (gp : GravitationalParam) (z : PhaseSpace) : Real :=
  semiMajorAxis mp gp z * Real.sqrt (1 - eccentricity mp gp z ^ (2 : Nat))

def signedArealVelocity (mp : MassParam) (gamma : Real -> PhaseSpace) (t : Real) : Real :=
  (1 / (2 * mp.m)) *
    inner ℝ
      ((1 / ‖angularMomentum (gamma 0)‖) • angularMomentum (gamma 0))
      (cross (gamma t).1 (gamma t).2)

def sweptAreaOn (mp : MassParam) (gamma : Real -> PhaseSpace) (t0 t1 : Real) : Real :=
  ∫ τ in t0..t1, signedArealVelocity mp gamma τ

structure HasConfigurationPeriod
    (mp : MassParam) (gp : GravitationalParam)
    (gamma : Real -> PhaseSpace) (T : Real) : Prop where
  pos : 0 < T
  periodic : Function.Periodic (fun t : Real => (gamma t).1) T
  minimal :
    ∀ {T' : Real}, 0 < T' →
      Function.Periodic (fun t : Real => (gamma t).1) T' →
      T ≤ T'

structure HasOrbitalPeriod
    (mp : MassParam) (gp : GravitationalParam)
    (gamma : Real -> PhaseSpace) (T : Real) : Prop
    extends HasConfigurationPeriod mp gp gamma T where
  sweptArea_eq :
    sweptAreaOn mp gamma 0 T =
      Real.pi * semiMajorAxis mp gp (gamma 0) * semiMinorAxis mp gp (gamma 0)

lemma keplerVectorField_contDiffAt_of_radialDist_ne_zero
    (mp : MassParam) (gp : GravitationalParam) (qp : PhaseSpace)
    (h : radialDist qp.1 ≠ 0) :
    ContDiffAt ℝ 1
      (fun qp : PhaseSpace =>
        ((1 / mp.m) • qp.2,
          (-gp.mu / (radialDist qp.1) ^ (3 : Nat)) • qp.1)) qp := by
  have hnorm : qp.1 ≠ 0 := by
    simpa [radialDist] using h
  have hqnorm : ContDiffAt ℝ 1 (fun qp : PhaseSpace => radialDist qp.1) qp := by
    simpa [radialDist] using (contDiffAt_norm ℝ hnorm).comp qp contDiffAt_fst
  have hpow : ContDiffAt ℝ 1 (fun qp : PhaseSpace => (radialDist qp.1) ^ (3 : Nat)) qp :=
    hqnorm.pow 3
  have hdiv : ContDiffAt ℝ 1 (fun qp : PhaseSpace => -gp.mu / (radialDist qp.1) ^ (3 : Nat)) qp := by
    exact contDiffAt_const.div hpow (by
      simpa [radialDist] using pow_ne_zero 3 (norm_ne_zero_iff.mpr hnorm))
  have hfst : ContDiffAt ℝ 1 (fun qp : PhaseSpace => (1 / mp.m) • qp.2) qp := by
    simpa using contDiffAt_snd.const_smul (1 / mp.m : Real)
  have hsnd :
      ContDiffAt ℝ 1 (fun qp : PhaseSpace => (-gp.mu / (radialDist qp.1) ^ (3 : Nat)) • qp.1) qp := by
    simpa using hdiv.smul contDiffAt_fst
  simpa using hfst.prodMk hsnd

lemma keplerVectorField_exists_lipschitzOnWith_of_radialDist_ne_zero
    (mp : MassParam) (gp : GravitationalParam) (qp : PhaseSpace)
    (h : radialDist qp.1 ≠ 0) :
    ∃ K, ∃ s ∈ nhds qp, LipschitzOnWith K (keplerVectorField mp gp) s := by
  let vf : PhaseSpace → PhaseSpace := fun qp =>
    ((1 / mp.m) • qp.2, (-gp.mu / (radialDist qp.1) ^ (3 : Nat)) • qp.1)
  have hvf : ContDiffAt ℝ 1 vf qp := by
    simpa [vf] using keplerVectorField_contDiffAt_of_radialDist_ne_zero mp gp qp h
  obtain ⟨K, t, ht, hLip⟩ := hvf.exists_lipschitzOnWith
  have hradCont : ContinuousAt (fun x : PhaseSpace => radialDist x.1) qp := by
    simpa [radialDist] using
      (continuous_fst.norm.continuousAt : ContinuousAt (fun x : PhaseSpace => ‖x.1‖) qp)
  have hnonzero : {x : PhaseSpace | radialDist x.1 ≠ 0} ∈ nhds qp := hradCont.eventually_ne h
  refine ⟨K, t ∩ {x : PhaseSpace | radialDist x.1 ≠ 0}, Filter.inter_mem ht hnonzero, ?_⟩
  intro x hx y hy
  have hxEq : keplerVectorField mp gp x = vf x := by
    refine Prod.ext ?_ ?_
    · simp [vf, keplerVectorField_fst]
    · simpa [vf] using
        keplerVectorField_snd_eq_smul_of_radialDist_ne_zero mp gp x hx.2
  have hyEq : keplerVectorField mp gp y = vf y := by
    refine Prod.ext ?_ ?_
    · simp [vf, keplerVectorField_fst]
    · simpa [vf] using
        keplerVectorField_snd_eq_smul_of_radialDist_ne_zero mp gp y hy.2
  simpa [hxEq, hyEq] using hLip hx.1 hy.1

lemma IsSolution.shift
    {mp : MassParam} {gp : GravitationalParam}
    {gamma : Real -> PhaseSpace} (hgamma : IsSolution mp gp gamma) (τ : Real) :
    IsSolution mp gp (fun t : Real => gamma (t + τ)) := by
  refine ⟨?_, ?_⟩
  · intro t
    simpa [add_assoc] using (hgamma.ode (t + τ)).comp_add_const t τ
  · intro t
    simpa [add_assoc] using hgamma.noCollision (t + τ)

lemma IsSolution.eventuallyEq_of_eq_at
    {mp : MassParam} {gp : GravitationalParam}
    {f g : Real -> PhaseSpace}
    (hf : IsSolution mp gp f) (hg : IsSolution mp gp g)
    {t0 : Real} (heq : f t0 = g t0) :
    f =ᶠ[nhds t0] g := by
  obtain ⟨K, s, hsN, hsLip⟩ :=
    keplerVectorField_exists_lipschitzOnWith_of_radialDist_ne_zero mp gp (f t0) (hf.noCollision t0)
  have hv :
      ∀ᶠ t in nhds t0,
        LipschitzOnWith K (fun z : PhaseSpace => keplerVectorField mp gp z) s := by
    exact Filter.Eventually.of_forall fun _ => hsLip
  have hfEv :
      ∀ᶠ t in nhds t0, HasDerivAt f (keplerVectorField mp gp (f t)) t ∧ f t ∈ s := by
    have hder :
        ∀ᶠ t in nhds t0, HasDerivAt f (keplerVectorField mp gp (f t)) t := by
      exact Filter.Eventually.of_forall hf.ode
    have hmem : ∀ᶠ t in nhds t0, f t ∈ s := by
      exact (hf.ode t0).continuousAt hsN
    exact hder.and hmem
  have hgEv :
      ∀ᶠ t in nhds t0, HasDerivAt g (keplerVectorField mp gp (g t)) t ∧ g t ∈ s := by
    have hder :
        ∀ᶠ t in nhds t0, HasDerivAt g (keplerVectorField mp gp (g t)) t := by
      exact Filter.Eventually.of_forall hg.ode
    have hsNg : s ∈ nhds (g t0) := by
      simpa [heq] using hsN
    have hmem : ∀ᶠ t in nhds t0, g t ∈ s := by
      exact (hg.ode t0).continuousAt hsNg
    exact hder.and hmem
  exact ODE_solution_unique_of_eventually hv hfEv hgEv heq

lemma IsSolution.eq_of_eq_at
    {mp : MassParam} {gp : GravitationalParam}
    {f g : Real -> PhaseSpace}
    (hf : IsSolution mp gp f) (hg : IsSolution mp gp g)
    {t0 : Real} (heq : f t0 = g t0) :
    f = g := by
  let S : Set Real := {t : Real | f t = g t}
  have hclosed : IsClosed S := by
    have hcf : Continuous f := continuous_iff_continuousAt.2 fun t => (hf.ode t).continuousAt
    have hcg : Continuous g := continuous_iff_continuousAt.2 fun t => (hg.ode t).continuousAt
    exact isClosed_eq hcf hcg
  have hopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    simpa [S] using hf.eventuallyEq_of_eq_at hg ht
  have huniv : S = Set.univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨t0, heq⟩
  funext t
  have ht : t ∈ S := by
    simp [huniv]
  exact ht

lemma phase_periodic_of_eq
    (mp : MassParam) (gp : GravitationalParam) (gamma : Real -> PhaseSpace)
    (hgamma : IsSolution mp gp gamma) {t1 t2 : Real}
    (heq : gamma t1 = gamma t2) :
    Function.Periodic gamma (t2 - t1) := by
  have hEq :
      (fun t : Real => gamma t) =
        fun t : Real => gamma (t + (t2 - t1)) := by
    apply IsSolution.eq_of_eq_at (hf := hgamma) (hg := hgamma.shift (t2 - t1)) (t0 := t1)
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using heq
  intro t
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using (congrFun hEq t).symm

lemma position_periodic_of_eq
    (mp : MassParam) (gp : GravitationalParam) (gamma : Real -> PhaseSpace)
    (hgamma : IsSolution mp gp gamma) (hL : angularMomentum (gamma 0) ≠ 0)
    {t1 t2 : Real} (hq : (gamma t1).1 = (gamma t2).1) :
    Function.Periodic (fun t : Real => (gamma t).1) (t2 - t1) := by
  have heq : gamma t1 = gamma t2 := phase_eq_of_position_eq mp gp gamma hgamma hL hq
  intro t
  exact congrArg Prod.fst (phase_periodic_of_eq mp gp gamma hgamma heq t)

lemma no_position_repeat_on_fundamental_period
    (mp : MassParam) (gp : GravitationalParam) (gamma : Real -> PhaseSpace)
    (hgamma : IsSolution mp gp gamma) (hL : angularMomentum (gamma 0) ≠ 0)
    {T : Real} (hT : HasConfigurationPeriod mp gp gamma T)
    {t1 t2 : Real} (ht10 : 0 ≤ t1) (ht12 : t1 < t2) (ht2T : t2 < T) :
    (gamma t1).1 ≠ (gamma t2).1 := by
  intro hq
  have hper := position_periodic_of_eq mp gp gamma hgamma hL hq
  have hpos : 0 < t2 - t1 := sub_pos.mpr ht12
  have hle : T ≤ t2 - t1 := hT.minimal hpos hper
  linarith

theorem configurationPeriod_injOn_position_Ico
    (mp : MassParam) (gp : GravitationalParam) (gamma : Real -> PhaseSpace)
    (hgamma : IsSolution mp gp gamma) (hL : angularMomentum (gamma 0) ≠ 0)
    {T : Real} (hT : HasConfigurationPeriod mp gp gamma T) :
    Set.InjOn (fun t : Real => (gamma t).1) (Set.Ico 0 T) := by
  intro t1 ht1 t2 ht2 hq
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact (no_position_repeat_on_fundamental_period mp gp gamma hgamma hL hT ht1.1 hlt ht2.2) hq
  · exact
      (no_position_repeat_on_fundamental_period mp gp gamma hgamma hL hT ht2.1 hgt ht1.2) hq.symm

theorem configurationPeriod_phase_periodic
    (mp : MassParam) (gp : GravitationalParam) (gamma : Real -> PhaseSpace)
    (hgamma : IsSolution mp gp gamma) (hL : angularMomentum (gamma 0) ≠ 0)
    {T : Real} (hT : HasConfigurationPeriod mp gp gamma T) :
    Function.Periodic gamma T := by
  intro t
  apply phase_eq_of_position_eq mp gp gamma hgamma hL
  simpa using hT.periodic t

theorem configurationPeriod_injOn_phase_Ico
    (mp : MassParam) (gp : GravitationalParam) (gamma : Real -> PhaseSpace)
    (hgamma : IsSolution mp gp gamma) (hL : angularMomentum (gamma 0) ≠ 0)
    {T : Real} (hT : HasConfigurationPeriod mp gp gamma T) :
    Set.InjOn gamma (Set.Ico 0 T) := by
  intro t1 ht1 t2 ht2 hq
  exact configurationPeriod_injOn_position_Ico mp gp gamma hgamma hL hT ht1 ht2 (congrArg Prod.fst hq)

theorem configurationPeriod_eq_or_endpoints_of_position_eq
    (mp : MassParam) (gp : GravitationalParam) (gamma : Real -> PhaseSpace)
    (hgamma : IsSolution mp gp gamma) (hL : angularMomentum (gamma 0) ≠ 0)
    {T : Real} (hT : HasConfigurationPeriod mp gp gamma T)
    {t1 t2 : Real} (ht1 : t1 ∈ Set.Icc 0 T) (ht2 : t2 ∈ Set.Icc 0 T)
    (hq : (gamma t1).1 = (gamma t2).1) :
    t1 = t2 ∨ (t1 = 0 ∧ t2 = T) ∨ (t1 = T ∧ t2 = 0) := by
  let s1 : Real := if t1 = T then 0 else t1
  let s2 : Real := if t2 = T then 0 else t2
  have hperiod0 : (gamma T).1 = (gamma 0).1 := by
    simpa using hT.periodic 0
  have hs1 : s1 ∈ Set.Ico 0 T := by
    by_cases ht1T : t1 = T
    · simp [s1, ht1T, hT.pos]
    · simp [s1, ht1T, ht1.1, lt_of_le_of_ne ht1.2 ht1T]
  have hs2 : s2 ∈ Set.Ico 0 T := by
    by_cases ht2T : t2 = T
    · simp [s2, ht2T, hT.pos]
    · simp [s2, ht2T, ht2.1, lt_of_le_of_ne ht2.2 ht2T]
  have hq1 : (gamma s1).1 = (gamma t1).1 := by
    by_cases ht1T : t1 = T
    · simp [s1, ht1T, hperiod0.symm]
    · simp [s1, ht1T]
  have hq2 : (gamma s2).1 = (gamma t2).1 := by
    by_cases ht2T : t2 = T
    · simp [s2, ht2T, hperiod0.symm]
    · simp [s2, ht2T]
  have hsEq : s1 = s2 := configurationPeriod_injOn_position_Ico mp gp gamma hgamma hL hT hs1 hs2 (by
    calc
      (gamma s1).1 = (gamma t1).1 := hq1
      _ = (gamma t2).1 := hq
      _ = (gamma s2).1 := hq2.symm)
  by_cases ht1T : t1 = T
  · by_cases ht2T : t2 = T
    · left
      simpa [ht1T, ht2T]
    · right
      right
      refine ⟨ht1T, ?_⟩
      have : s2 = 0 := by simpa [s1, s2, ht1T, ht2T] using hsEq.symm
      simpa [s2, ht2T] using this
  · by_cases ht2T : t2 = T
    · right
      left
      refine ⟨?_, ht2T⟩
      have : s1 = 0 := by simpa [s1, s2, ht1T, ht2T] using hsEq
      simpa [s1, ht1T] using this
    · left
      simpa [s1, s2, ht1T, ht2T] using hsEq

lemma position_eq_of_adapted_coords_eq
    (L0 eA eB q1 q2 : Vec3) (hL : L0 ≠ 0)
    (hLeA : inner ℝ L0 eA = 0) (hLeB : inner ℝ L0 eB = 0)
    (heA : inner ℝ eA eA = 1) (heB : inner ℝ eB eB = 1)
    (heAeB : inner ℝ eA eB = 0)
    (hq1 : inner ℝ L0 q1 = 0) (hq2 : inner ℝ L0 q2 = 0)
    (hx : inner ℝ eA q1 = inner ℝ eA q2)
    (hy : inner ℝ eB q1 = inner ℝ eB q2) :
    q1 = q2 := by
  let eL : Vec3 := (1 / ‖L0‖) • L0
  have hnormL0 : ‖L0‖ ≠ 0 := norm_ne_zero_iff.mpr hL
  have heL : inner ℝ eL eL = 1 := by
    dsimp [eL]
    rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp [hnormL0]
  have hA_L0 : inner ℝ eA L0 = 0 := by
    simpa [real_inner_comm] using hLeA
  have hB_L0 : inner ℝ eB L0 = 0 := by
    simpa [real_inner_comm] using hLeB
  have hAeL : inner ℝ eA eL = 0 := by
    dsimp [eL]
    rw [real_inner_smul_right]
    simp [hA_L0]
  have hBeL : inner ℝ eB eL = 0 := by
    dsimp [eL]
    rw [real_inner_smul_right]
    simp [hB_L0]
  let v : Fin 3 → Vec3 := ![eA, eB, eL]
  have hv : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j
    · simpa [v] using heA
    · simpa [v] using heAeB
    · simpa [v, real_inner_comm] using hAeL
    · simpa [v, real_inner_comm] using heAeB
    · simpa [v] using heB
    · simpa [v, real_inner_comm] using hBeL
    · simpa [v, real_inner_comm] using hAeL
    · simpa [v, real_inner_comm] using hBeL
    · simpa [v] using heL
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ Vec3 := by
    simp [Vec3]
  let B : Module.Basis (Fin 3) ℝ Vec3 :=
    basisOfOrthonormalOfCardEqFinrank hv hcard
  have hBv : (B : Fin 3 → Vec3) = v := by
    simp [B]
  have hBorth : Orthonormal ℝ (B : Fin 3 → Vec3) := by
    simpa [hBv] using hv
  let oB : OrthonormalBasis (Fin 3) ℝ Vec3 := B.toOrthonormalBasis hBorth
  have hoBv : (oB : Fin 3 → Vec3) = v := by
    rw [Module.Basis.coe_toOrthonormalBasis, hBv]
  have heLq1 : inner ℝ eL q1 = 0 := by
    dsimp [eL]
    rw [real_inner_smul_left]
    simp [hq1]
  have heLq2 : inner ℝ eL q2 = 0 := by
    dsimp [eL]
    rw [real_inner_smul_left]
    simp [hq2]
  apply oB.repr.injective
  ext i
  fin_cases i
  · simpa [OrthonormalBasis.repr_apply_apply, hoBv, v] using hx
  · simpa [OrthonormalBasis.repr_apply_apply, hoBv, v] using hy
  · simpa [OrthonormalBasis.repr_apply_apply, hoBv, v] using heLq1.trans heLq2.symm

theorem configurationPeriod_eq_or_endpoints_of_adapted_coords_eq
    (mp : MassParam) (gp : GravitationalParam) (gamma : Real -> PhaseSpace)
    (hgamma : IsSolution mp gp gamma) (hL : angularMomentum (gamma 0) ≠ 0)
    {T : Real} (hT : HasConfigurationPeriod mp gp gamma T)
    {eA eB : Vec3}
    (hLeA : inner ℝ (angularMomentum (gamma 0)) eA = 0)
    (hLeB : inner ℝ (angularMomentum (gamma 0)) eB = 0)
    (heA : inner ℝ eA eA = 1) (heB : inner ℝ eB eB = 1)
    (heAeB : inner ℝ eA eB = 0)
    {t1 t2 : Real} (ht1 : t1 ∈ Set.Icc 0 T) (ht2 : t2 ∈ Set.Icc 0 T)
    (hx : inner ℝ eA (gamma t1).1 = inner ℝ eA (gamma t2).1)
    (hy : inner ℝ eB (gamma t1).1 = inner ℝ eB (gamma t2).1) :
    t1 = t2 ∨ (t1 = 0 ∧ t2 = T) ∨ (t1 = T ∧ t2 = 0) := by
  have hq1 : inner ℝ (angularMomentum (gamma 0)) (gamma t1).1 = 0 := by
    have hLconst := angularMomentum_const hgamma t1
    have hperp : inner ℝ (angularMomentum (gamma t1)) (gamma t1).1 = 0 := by
      simp [angularMomentum, inner_fin3, cross, cross_apply]
      ring
    calc
      inner ℝ (angularMomentum (gamma 0)) (gamma t1).1
          = inner ℝ (angularMomentum (gamma t1)) (gamma t1).1 := by rw [hLconst]
      _ = 0 := hperp
  have hq2 : inner ℝ (angularMomentum (gamma 0)) (gamma t2).1 = 0 := by
    have hLconst := angularMomentum_const hgamma t2
    have hperp : inner ℝ (angularMomentum (gamma t2)) (gamma t2).1 = 0 := by
      simp [angularMomentum, inner_fin3, cross, cross_apply]
      ring
    calc
      inner ℝ (angularMomentum (gamma 0)) (gamma t2).1
          = inner ℝ (angularMomentum (gamma t2)) (gamma t2).1 := by rw [hLconst]
      _ = 0 := hperp
  have hpos : (gamma t1).1 = (gamma t2).1 := by
    exact position_eq_of_adapted_coords_eq
      (angularMomentum (gamma 0)) eA eB (gamma t1).1 (gamma t2).1 hL
      hLeA hLeB heA heB heAeB hq1 hq2 hx hy
  exact configurationPeriod_eq_or_endpoints_of_position_eq mp gp gamma hgamma hL hT ht1 ht2 hpos

theorem configurationPeriod_eq_or_endpoints_of_same_standardEllipse_angle
    (mp : MassParam) (gp : GravitationalParam) (gamma : Real -> PhaseSpace)
    (hgamma : IsSolution mp gp gamma) (hL : angularMomentum (gamma 0) ≠ 0)
    {T : Real} (hT : HasConfigurationPeriod mp gp gamma T)
    {eA eB : Vec3}
    (hLeA : inner ℝ (angularMomentum (gamma 0)) eA = 0)
    (hLeB : inner ℝ (angularMomentum (gamma 0)) eB = 0)
    (heA : inner ℝ eA eA = 1) (heB : inner ℝ eB eB = 1)
    (heAeB : inner ℝ eA eB = 0)
    {a b e θ1 θ2 : Real} {t1 t2 : Real}
    (ht1 : t1 ∈ Set.Icc 0 T) (ht2 : t2 ∈ Set.Icc 0 T)
    (hx1 : inner ℝ eA (gamma t1).1 = a * (Real.cos θ1 - e))
    (hy1 : inner ℝ eB (gamma t1).1 = b * Real.sin θ1)
    (hx2 : inner ℝ eA (gamma t2).1 = a * (Real.cos θ2 - e))
    (hy2 : inner ℝ eB (gamma t2).1 = b * Real.sin θ2)
    (hcos : Real.cos θ1 = Real.cos θ2)
    (hsin : Real.sin θ1 = Real.sin θ2) :
    t1 = t2 ∨ (t1 = 0 ∧ t2 = T) ∨ (t1 = T ∧ t2 = 0) := by
  apply configurationPeriod_eq_or_endpoints_of_adapted_coords_eq
    mp gp gamma hgamma hL hT hLeA hLeB heA heB heAeB ht1 ht2
  · calc
      inner ℝ eA (gamma t1).1 = a * (Real.cos θ1 - e) := hx1
      _ = a * (Real.cos θ2 - e) := by rw [hcos]
      _ = inner ℝ eA (gamma t2).1 := hx2.symm
  · calc
      inner ℝ eB (gamma t1).1 = b * Real.sin θ1 := hy1
      _ = b * Real.sin θ2 := by rw [hsin]
      _ = inner ℝ eB (gamma t2).1 := hy2.symm

theorem kepler_second_law
    (mp : MassParam) (gp : GravitationalParam) (gamma : Real -> PhaseSpace)
    (hgamma : IsSolution mp gp gamma) (hL : angularMomentum (gamma 0) ≠ 0) :
    ∀ t : Real,
      signedArealVelocity mp gamma t =
        ‖angularMomentum (gamma 0)‖ / (2 * mp.m) := by
  intro t
  have hLconst := angularMomentum_const hgamma t
  have hnorm0 : ‖angularMomentum (gamma 0)‖ ≠ 0 := norm_ne_zero_iff.mpr hL
  unfold signedArealVelocity
  rw [show cross (gamma t).1 (gamma t).2 = angularMomentum (gamma 0) by
        simpa [angularMomentum] using hLconst]
  rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
  field_simp [hnorm0, ne_of_gt mp.hm]

lemma laplaceLenz_norm_sq (mp : MassParam) (gp : GravitationalParam) (z : PhaseSpace) (hr : radialDist z.1 ≠ 0) :
    ‖laplaceLenz mp gp z‖ ^ 2 =
      (mp.m * gp.mu) ^ 2 + 2 * mp.m * energy mp gp z * ‖angularMomentum z‖ ^ 2 := by
  have hbi := basic_identities_L_A mp gp z hr
  exact hbi.2.2.2

lemma ecc_lt_one_of_h_neg
    (mp : MassParam) (gp : GravitationalParam) (z : PhaseSpace)
    (hE : energy mp gp z < 0) (hL : angularMomentum z ≠ 0) (hr : radialDist z.1 ≠ 0) :
    ‖laplaceLenz mp gp z‖ < mp.m * gp.mu := by
  have hsq := laplaceLenz_norm_sq mp gp z hr
  have h2mE : 2 * mp.m * energy mp gp z < 0 := by
    nlinarith [hE, mp.hm]
  have hLpos : 0 < ‖angularMomentum z‖ ^ (2 : Nat) := by
    exact pow_pos (norm_pos_iff.mpr hL) 2
  have hterm_neg : 2 * mp.m * energy mp gp z * ‖angularMomentum z‖ ^ 2 < 0 := by
    apply mul_neg_of_neg_of_pos
    · exact h2mE
    · exact hLpos
  have hsq_lt : ‖laplaceLenz mp gp z‖ ^ (2 : Nat) < (mp.m * gp.mu) ^ (2 : Nat) := by
    rw [hsq]
    nlinarith
  have hmμ : 0 < mp.m * gp.mu := by nlinarith [mp.hm, gp.hmu]
  nlinarith [hsq_lt, hmμ, sq_nonneg ‖laplaceLenz mp gp z‖]

lemma eccentricity_nonneg (mp : MassParam) (gp : GravitationalParam) (z : PhaseSpace) :
    0 ≤ eccentricity mp gp z := by
  unfold eccentricity
  exact div_nonneg (norm_nonneg _) (show 0 ≤ mp.m * gp.mu by nlinarith [mp.hm, gp.hmu])

lemma eccentricity_lt_one
    (mp : MassParam) (gp : GravitationalParam) (z : PhaseSpace)
    (hE : energy mp gp z < 0) (hL : angularMomentum z ≠ 0) (hr : radialDist z.1 ≠ 0) :
    eccentricity mp gp z < 1 := by
  have hmμ : 0 < mp.m * gp.mu := by nlinarith [mp.hm, gp.hmu]
  unfold eccentricity
  have hlt := ecc_lt_one_of_h_neg mp gp z hE hL hr
  exact (div_lt_one hmμ).2 hlt

lemma planarity
    (mp : MassParam) (gp : GravitationalParam) (gamma : Real -> PhaseSpace)
    (hgamma : IsSolution mp gp gamma) (_hL : angularMomentum (gamma 0) ≠ 0)
    (t : Real) :
    inner ℝ (angularMomentum (gamma 0)) (gamma t).1 = 0 ∧ inner ℝ (angularMomentum (gamma 0)) (gamma t).2 = 0 := by
  have hLconst := angularMomentum_const hgamma t
  have hperp :
      inner ℝ (angularMomentum (gamma t)) (gamma t).1 = 0 ∧
        inner ℝ (angularMomentum (gamma t)) (gamma t).2 = 0 := by
    constructor
    · simp [angularMomentum]; rw [real_inner_comm]; exact inner_cross_self _ _
    · simp [angularMomentum, inner_fin3, cross, cross_apply]
      ring
  constructor
  · calc
      inner ℝ (angularMomentum (gamma 0)) (gamma t).1
          = inner ℝ (angularMomentum (gamma t)) (gamma t).1 := by rw [hLconst]
      _ = 0 := hperp.1
  · calc
      inner ℝ (angularMomentum (gamma 0)) (gamma t).2
          = inner ℝ (angularMomentum (gamma t)) (gamma t).2 := by rw [hLconst]
      _ = 0 := hperp.2

lemma semi_major_axis (mp : MassParam) (gp : GravitationalParam) (z : PhaseSpace)
    (hE : energy mp gp z < 0) :
    0 < semiMajorAxis mp gp z := by
  have hden : 2 * energy mp gp z < 0 := by nlinarith
  have hdiv : gp.mu / (2 * energy mp gp z) < 0 := by
    exact div_neg_of_pos_of_neg gp.hmu hden
  unfold semiMajorAxis
  nlinarith

lemma semiLatusRectum_eq_semiMajorAxis_mul_one_sub_eccentricity_sq
    (mp : MassParam) (gp : GravitationalParam) (z : PhaseSpace)
    (hE : energy mp gp z < 0) (hr : radialDist z.1 ≠ 0) :
    semiLatusRectum mp gp z =
      semiMajorAxis mp gp z * (1 - eccentricity mp gp z ^ (2 : Nat)) := by
  have hm : mp.m ≠ 0 := ne_of_gt mp.hm
  have hμ : gp.mu ≠ 0 := ne_of_gt gp.hmu
  have hmμ : mp.m * gp.mu ≠ 0 := mul_ne_zero (ne_of_gt mp.hm) (ne_of_gt gp.hmu)
  have hEnz : energy mp gp z ≠ 0 := ne_of_lt hE
  have hsq := laplaceLenz_norm_sq mp gp z hr
  unfold semiLatusRectum semiMajorAxis eccentricity
  rw [pow_two, div_pow, hsq]
  field_simp [hm, hμ, hmμ, hEnz]
  ring_nf

lemma eccentricity_sq_eq_one_add_energy_term
    (mp : MassParam) (gp : GravitationalParam) (z : PhaseSpace)
    (hr : radialDist z.1 ≠ 0) :
    eccentricity mp gp z ^ (2 : Nat) =
      1 +
        2 * energy mp gp z * ‖angularMomentum z‖ ^ (2 : Nat) /
          (mp.m * gp.mu ^ (2 : Nat)) := by
  have hm : mp.m ≠ 0 := ne_of_gt mp.hm
  have hμ : gp.mu ≠ 0 := ne_of_gt gp.hmu
  have hmμ : mp.m * gp.mu ≠ 0 := mul_ne_zero hm hμ
  have hsq := laplaceLenz_norm_sq mp gp z hr
  unfold eccentricity
  rw [pow_two]
  calc
    (‖laplaceLenz mp gp z‖ / (mp.m * gp.mu)) * (‖laplaceLenz mp gp z‖ / (mp.m * gp.mu))
        = ‖laplaceLenz mp gp z‖ ^ (2 : Nat) / (mp.m * gp.mu) ^ (2 : Nat) := by
            field_simp [hmμ]
    _ =
        ((mp.m * gp.mu) ^ (2 : Nat) +
            2 * mp.m * energy mp gp z * ‖angularMomentum z‖ ^ (2 : Nat)) /
          (mp.m * gp.mu) ^ (2 : Nat) := by rw [hsq]
    _ =
        1 +
          2 * energy mp gp z * ‖angularMomentum z‖ ^ (2 : Nat) /
            (mp.m * gp.mu ^ (2 : Nat)) := by
            field_simp [hm, hμ, hmμ]

lemma semiMinorAxis_sq
    (mp : MassParam) (gp : GravitationalParam) (z : PhaseSpace)
    (hE : energy mp gp z < 0) (hL : angularMomentum z ≠ 0) (hr : radialDist z.1 ≠ 0) :
    semiMinorAxis mp gp z ^ (2 : Nat) =
      semiMajorAxis mp gp z * semiLatusRectum mp gp z := by
  have he0 : 0 ≤ eccentricity mp gp z := eccentricity_nonneg mp gp z
  have he1 : eccentricity mp gp z < 1 := eccentricity_lt_one mp gp z hE hL hr
  have hnonneg : 0 ≤ 1 - eccentricity mp gp z ^ (2 : Nat) := by
    nlinarith
  have hsqrt :
      Real.sqrt (1 - eccentricity mp gp z ^ (2 : Nat)) *
          Real.sqrt (1 - eccentricity mp gp z ^ (2 : Nat)) =
        1 - eccentricity mp gp z ^ (2 : Nat) := by
    nlinarith [Real.sq_sqrt hnonneg]
  calc
    semiMinorAxis mp gp z ^ (2 : Nat)
        = semiMajorAxis mp gp z ^ (2 : Nat) *
            (1 - eccentricity mp gp z ^ (2 : Nat)) := by
            let x := 1 - eccentricity mp gp z ^ (2 : Nat)
            unfold semiMinorAxis
            rw [pow_two]
            calc
              (semiMajorAxis mp gp z * Real.sqrt x) * (semiMajorAxis mp gp z * Real.sqrt x)
                  = semiMajorAxis mp gp z ^ (2 : Nat) * (Real.sqrt x) ^ (2 : Nat) := by
                      simp [pow_two]
                      ring
              _ = semiMajorAxis mp gp z ^ (2 : Nat) * x := by
                    rw [Real.sq_sqrt (by simpa [x] using hnonneg)]
              _ = semiMajorAxis mp gp z ^ (2 : Nat) *
                    (1 - eccentricity mp gp z ^ (2 : Nat)) := by
                    simp [x]
    _ = semiMajorAxis mp gp z * semiLatusRectum mp gp z := by
          rw [semiLatusRectum_eq_semiMajorAxis_mul_one_sub_eccentricity_sq mp gp z hE hr]
          ring

lemma semiMajorAxis_eq_semiLatusRectum_div_one_sub_eccentricity_sq
    (mp : MassParam) (gp : GravitationalParam) (z : PhaseSpace)
    (hE : energy mp gp z < 0) (hL : angularMomentum z ≠ 0) (hr : radialDist z.1 ≠ 0) :
    semiMajorAxis mp gp z =
      semiLatusRectum mp gp z / (1 - eccentricity mp gp z ^ (2 : Nat)) := by
  have hden : 1 - eccentricity mp gp z ^ (2 : Nat) ≠ 0 := by
    have he0 := eccentricity_nonneg mp gp z
    have he1 := eccentricity_lt_one mp gp z hE hL hr
    have hs : eccentricity mp gp z ^ (2 : Nat) < 1 := by
      nlinarith
    exact sub_ne_zero.mpr (by linarith)
  apply (eq_div_iff hden).2
  simpa [mul_comm] using
    (semiLatusRectum_eq_semiMajorAxis_mul_one_sub_eccentricity_sq mp gp z hE hr).symm

lemma semiMinorAxis_pos
    (mp : MassParam) (gp : GravitationalParam) (z : PhaseSpace)
    (hE : energy mp gp z < 0) (hL : angularMomentum z ≠ 0) (hr : radialDist z.1 ≠ 0) :
    0 < semiMinorAxis mp gp z := by
  have ha : 0 < semiMajorAxis mp gp z := semi_major_axis mp gp z hE
  have he0 : 0 ≤ eccentricity mp gp z := eccentricity_nonneg mp gp z
  have he1 : eccentricity mp gp z < 1 := eccentricity_lt_one mp gp z hE hL hr
  have hs : 0 < 1 - eccentricity mp gp z ^ (2 : Nat) := by
    nlinarith
  have hsqrt : 0 < Real.sqrt (1 - eccentricity mp gp z ^ (2 : Nat)) := Real.sqrt_pos.2 hs
  unfold semiMinorAxis
  exact mul_pos ha hsqrt

lemma semiLatusRectum_eq_semiMinorAxis_sq_div_semiMajorAxis
    (mp : MassParam) (gp : GravitationalParam) (z : PhaseSpace)
    (hE : energy mp gp z < 0) (hL : angularMomentum z ≠ 0) (hr : radialDist z.1 ≠ 0) :
    semiLatusRectum mp gp z =
      semiMinorAxis mp gp z ^ (2 : Nat) / semiMajorAxis mp gp z := by
  have ha : semiMajorAxis mp gp z ≠ 0 := ne_of_gt (semi_major_axis mp gp z hE)
  apply (eq_div_iff ha).2
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (semiMinorAxis_sq mp gp z hE hL hr).symm

theorem kepler_first_law_orbit_equation_exact
    (mp : MassParam) (gp : GravitationalParam) (gamma : Real -> PhaseSpace)
    (hgamma : IsSolution mp gp gamma) (hL : angularMomentum (gamma 0) ≠ 0) :
    let z0 := gamma 0
    let A0 := laplaceLenz mp gp z0
    let l := semiLatusRectum mp gp z0
    let e := eccentricity mp gp z0
    (A0 = 0 → ∀ t : Real, radialDist (gamma t).1 = l) ∧
      (A0 ≠ 0 →
        ∀ t : Real,
          let q := (gamma t).1
          let r := radialDist q
          let u := (1 / r) • q
          r = l / (1 + e * inner ℝ u ((1 / ‖A0‖) • A0))) := by
  dsimp
  set z0 : PhaseSpace := gamma 0
  set A0 : Vec3 := laplaceLenz mp gp z0
  set l : Real := semiLatusRectum mp gp z0
  set e : Real := eccentricity mp gp z0
  constructor
  · intro hzero t
    simpa [A0, l, z0] using orbit_circle_of_zero_laplaceLenz mp gp gamma hgamma hzero t
  · intro hne t
    set q : Vec3 := (gamma t).1
    set r : Real := radialDist q
    let u : Vec3 := (1 / r) • q
    have hr : r ≠ 0 := by simpa [q, r] using hgamma.noCollision t
    have hmμ : mp.m * gp.mu ≠ 0 := mul_ne_zero (ne_of_gt mp.hm) (ne_of_gt gp.hmu)
    have hnormL0 : ‖angularMomentum z0‖ ≠ 0 := norm_ne_zero_iff.mpr (by simpa [z0] using hL)
    have hkepler := kepler_first_law mp gp gamma hgamma t
    have hcoeff0 :
        inner ℝ A0 q = ‖angularMomentum z0‖ ^ (2 : Nat) - (mp.m * gp.mu) * r := by
      simpa [A0, q, r, z0] using hkepler.1
    have hqeq : r • u = q := by
      dsimp [u]
      calc
        r • ((1 / r) • q) = (r * (1 / r)) • q := by rw [smul_smul]
        _ = (1 : Real) • q := by
              congr 1
              field_simp [hr]
        _ = q := by simp
    have hinner : inner ℝ A0 q = r * inner ℝ A0 u := by
      calc
        inner ℝ A0 q = inner ℝ A0 (r • u) := by rw [hqeq]
        _ = r * inner ℝ A0 u := by rw [real_inner_smul_right]
    have hcoeff1 :
        r * inner ℝ A0 u = ‖angularMomentum z0‖ ^ (2 : Nat) - (mp.m * gp.mu) * r := by
      simpa [hinner] using hcoeff0
    have hmul : r * (mp.m * gp.mu + inner ℝ A0 u) = ‖angularMomentum z0‖ ^ (2 : Nat) := by
      calc
        r * (mp.m * gp.mu + inner ℝ A0 u)
            = (mp.m * gp.mu) * r + r * inner ℝ A0 u := by ring
        _ = (mp.m * gp.mu) * r + (‖angularMomentum z0‖ ^ (2 : Nat) - (mp.m * gp.mu) * r) := by
              rw [hcoeff1]
        _ = ‖angularMomentum z0‖ ^ (2 : Nat) := by ring
    have hden :
        mp.m * gp.mu + inner ℝ A0 u ≠ 0 := by
      intro hz
      have hzeroL : ‖angularMomentum z0‖ ^ (2 : Nat) = 0 := by
        simpa [hz] using hmul.symm
      have hnorm_zero : ‖angularMomentum z0‖ = 0 := by
        exact eq_zero_of_pow_eq_zero hzeroL
      exact hL (norm_eq_zero.mp hnorm_zero)
    have horbit := kepler_first_law_orbit_equation mp gp gamma hgamma t hr hden
    simpa [A0, l, e, z0, q, r, u, eccentricity] using horbit.2 hne

theorem kepler_first_law_geometric_data
    (mp : MassParam) (gp : GravitationalParam) (gamma : Real -> PhaseSpace)
    (hgamma : IsSolution mp gp gamma) (hE : energy mp gp (gamma 0) < 0)
    (hL : angularMomentum (gamma 0) ≠ 0) :
    let z0 := gamma 0
    let A0 := laplaceLenz mp gp z0
    let L0 := angularMomentum z0
    let e := eccentricity mp gp z0
    let l := semiLatusRectum mp gp z0
    let a := semiMajorAxis mp gp z0
    let b := semiMinorAxis mp gp z0
    (∀ t : Real, inner ℝ L0 (gamma t).1 = 0) ∧
      0 ≤ e ∧ e < 1 ∧ 0 < a ∧ 0 < b ∧
      l = a * (1 - e ^ (2 : Nat)) ∧
      b ^ (2 : Nat) = a * l ∧
      (A0 = 0 → ∀ t : Real, radialDist (gamma t).1 = l) ∧
      (A0 ≠ 0 →
        ∀ t : Real,
          let q := (gamma t).1
          let r := radialDist q
          let u := (1 / r) • q
          r = l / (1 + e * inner ℝ u ((1 / ‖A0‖) • A0))) := by
  dsimp
  set z0 : PhaseSpace := gamma 0
  set A0 : Vec3 := laplaceLenz mp gp z0
  set L0 : Vec3 := angularMomentum z0
  set e : Real := eccentricity mp gp z0
  set l : Real := semiLatusRectum mp gp z0
  set a : Real := semiMajorAxis mp gp z0
  set b : Real := semiMinorAxis mp gp z0
  have horbit := kepler_first_law_orbit_equation_exact mp gp gamma hgamma hL
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    simpa [L0, z0] using (planarity mp gp gamma hgamma hL t).1
  · simpa [e, z0] using eccentricity_nonneg mp gp z0
  · simpa [e, z0] using eccentricity_lt_one mp gp z0 hE hL (hgamma.noCollision 0)
  · simpa [a, z0] using semi_major_axis mp gp z0 hE
  · simpa [b, z0] using semiMinorAxis_pos mp gp z0 hE hL (hgamma.noCollision 0)
  · simpa [l, a, e, z0] using
      semiLatusRectum_eq_semiMajorAxis_mul_one_sub_eccentricity_sq mp gp z0 hE (hgamma.noCollision 0)
  · simpa [a, b, l, z0, L0] using
      semiMinorAxis_sq mp gp z0 hE (by simpa [z0, L0] using hL) (hgamma.noCollision 0)
  · simpa [A0, l, e, z0] using horbit

theorem kepler_first_law_exact
    (mp : MassParam) (gp : GravitationalParam) (gamma : Real -> PhaseSpace)
    (hgamma : IsSolution mp gp gamma) (hE : energy mp gp (gamma 0) < 0)
    (hL : angularMomentum (gamma 0) ≠ 0) :
    let z0 := gamma 0
    let A0 := laplaceLenz mp gp z0
    let L0 := angularMomentum z0
    let e := eccentricity mp gp z0
    let l := semiLatusRectum mp gp z0
    let a := semiMajorAxis mp gp z0
    let b := semiMinorAxis mp gp z0
    (∀ t : Real, inner ℝ L0 (gamma t).1 = 0) ∧
      e = ‖A0‖ / (mp.m * gp.mu) ∧
      l = ‖L0‖ ^ (2 : Nat) / (mp.m * gp.mu) ∧
      a = -(gp.mu / (2 * energy mp gp z0)) ∧
      0 ≤ e ∧ e < 1 ∧ 0 < a ∧ 0 < b ∧
      l = a * (1 - e ^ (2 : Nat)) ∧
      b ^ (2 : Nat) = a * l ∧
      (A0 = 0 → ∀ t : Real, radialDist (gamma t).1 = l) ∧
      (A0 ≠ 0 →
        ∀ t : Real,
          let q := (gamma t).1
          let r := radialDist q
          let u := (1 / r) • q
          r = l / (1 + e * inner ℝ u ((1 / ‖A0‖) • A0))) := by
  dsimp
  set z0 : PhaseSpace := gamma 0
  set A0 : Vec3 := laplaceLenz mp gp z0
  set L0 : Vec3 := angularMomentum z0
  set e : Real := eccentricity mp gp z0
  set l : Real := semiLatusRectum mp gp z0
  set a : Real := semiMajorAxis mp gp z0
  set b : Real := semiMinorAxis mp gp z0
  have hgeom := kepler_first_law_geometric_data mp gp gamma hgamma hE hL
  rcases hgeom with ⟨hplane, he0, he1, ha, hb, hl, hb_sq, hcircle, horbit⟩
  refine ⟨hplane, rfl, rfl, rfl, he0, he1, ha, hb, hl, hb_sq, hcircle, ?_⟩
  intro hne t
  simpa [A0, e, l, z0] using horbit hne t

theorem kepler_first_law_cartesian_ellipse
    (mp : MassParam) (gp : GravitationalParam) (gamma : Real -> PhaseSpace)
    (hgamma : IsSolution mp gp gamma) (hE : energy mp gp (gamma 0) < 0)
    (hL : angularMomentum (gamma 0) ≠ 0) :
    let z0 := gamma 0
    let A0 := laplaceLenz mp gp z0
    let L0 := angularMomentum z0
    let e := eccentricity mp gp z0
    let a := semiMajorAxis mp gp z0
    let b := semiMinorAxis mp gp z0
    (A0 = 0 → ∀ t : Real, radialDist (gamma t).1 = a ∧ a = b) ∧
      (A0 ≠ 0 →
        ∃ eA eB : Vec3,
          inner ℝ L0 eA = 0 ∧
          inner ℝ L0 eB = 0 ∧
          inner ℝ eA eA = 1 ∧
          inner ℝ eB eB = 1 ∧
          inner ℝ eA eB = 0 ∧
          a ^ (2 : Nat) - b ^ (2 : Nat) = (a * e) ^ (2 : Nat) ∧
          ∀ t : Real,
            let q := (gamma t).1
            let x := inner ℝ eA q
            let y := inner ℝ eB q
            ((x + a * e) ^ (2 : Nat)) / (a ^ (2 : Nat)) +
                (y ^ (2 : Nat)) / (b ^ (2 : Nat)) =
              1) := by
  dsimp
  set z0 : PhaseSpace := gamma 0
  set A0 : Vec3 := laplaceLenz mp gp z0
  set L0 : Vec3 := angularMomentum z0
  set e : Real := eccentricity mp gp z0
  set l : Real := semiLatusRectum mp gp z0
  set a : Real := semiMajorAxis mp gp z0
  set b : Real := semiMinorAxis mp gp z0
  have hexact := kepler_first_law_exact mp gp gamma hgamma hE hL
  rcases hexact with ⟨hplane, hedef, hldef, hadef, he0, he1, ha, hb, hl, hb_sq, hcircle, _horbit⟩
  constructor
  · intro hA0 t
    have he_zero : e = 0 := by
      simp [e, A0, z0, eccentricity, hA0]
    have hl_eq_a : l = a := by
      simpa [l, a, e, z0, he_zero] using hl
    have hb_eq_a : a = b := by
      have hsq : b ^ (2 : Nat) = a ^ (2 : Nat) := by
        nlinarith [hb_sq, hl_eq_a]
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hab | hab
      · exact hab.symm
      · nlinarith [ha, hb, hab]
    refine ⟨?_, hb_eq_a⟩
    calc
      radialDist (gamma t).1 = l := hcircle hA0 t
      _ = a := hl_eq_a
  · intro hA0
    have hA0norm : ‖A0‖ ≠ 0 := norm_ne_zero_iff.mpr hA0
    have hL0norm : ‖L0‖ ≠ 0 := norm_ne_zero_iff.mpr (by simpa [L0, z0] using hL)
    have hmμ : mp.m * gp.mu ≠ 0 := mul_ne_zero (ne_of_gt mp.hm) (ne_of_gt gp.hmu)
    have hLA0 :
        inner ℝ L0 A0 = 0 := by
      simpa [L0, A0, z0] using (basic_identities_L_A mp gp z0 (hgamma.noCollision 0)).1
    let eA : Vec3 := (1 / ‖A0‖) • A0
    let eL : Vec3 := (1 / ‖L0‖) • L0
    let eB : Vec3 := cross eL eA
    have heA_unit : inner ℝ eA eA = 1 := by
      dsimp [eA]
      rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp [hA0norm]
    have heL_unit : inner ℝ eL eL = 1 := by
      dsimp [eL]
      rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp [hL0norm]
    have heL_eA : inner ℝ eL eA = 0 := by
      dsimp [eL, eA]
      rw [real_inner_smul_left, real_inner_smul_right, hLA0]
      ring
    have heL_eB : inner ℝ eL eB = 0 := by
      dsimp [eB]
      simpa using inner_cross_left_zero eL eA
    have heA_eB : inner ℝ eA eB = 0 := by
      dsimp [eB]
      simpa using inner_cross_right_zero eL eA
    have heB_unit : inner ℝ eB eB = 1 := by
      have hnorm_sq : ‖eB‖ ^ (2 : Nat) = 1 := by
        calc
          ‖eB‖ ^ (2 : Nat)
              = ‖eL‖ ^ (2 : Nat) * ‖eA‖ ^ (2 : Nat) - (inner ℝ eL eA) ^ (2 : Nat) := by
                  simpa [eB] using norm_cross_sq eL eA
          _ = 1 := by
                rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, heL_unit, heA_unit,
                  heL_eA]
                ring
      simpa [real_inner_self_eq_norm_sq] using hnorm_sq
    have hfocus :
        a ^ (2 : Nat) - b ^ (2 : Nat) = (a * e) ^ (2 : Nat) := by
      nlinarith [hl, hb_sq]
    let v : Fin 3 → Vec3 := ![eA, eB, eL]
    have hv : Orthonormal ℝ v := by
      rw [orthonormal_iff_ite]
      intro i j
      fin_cases i <;> fin_cases j
      · simpa [v] using heA_unit
      · simpa [v] using heA_eB
      · simpa [v, real_inner_comm] using heL_eA
      · simpa [v, real_inner_comm] using heA_eB
      · simpa [v] using heB_unit
      · simpa [v, real_inner_comm] using heL_eB
      · simpa [v] using heL_eA
      · simpa [v] using heL_eB
      · simpa [v] using heL_unit
    have hcard : Fintype.card (Fin 3) = Module.finrank ℝ Vec3 := by
      simp [Vec3]
    let B : Module.Basis (Fin 3) ℝ Vec3 := basisOfOrthonormalOfCardEqFinrank hv hcard
    have hBv : (B : Fin 3 → Vec3) = v := by
      simp [B]
    have hBorth : Orthonormal ℝ (B : Fin 3 → Vec3) := by
      simpa [hBv] using hv
    let oB : OrthonormalBasis (Fin 3) ℝ Vec3 := B.toOrthonormalBasis hBorth
    have hoBv : (oB : Fin 3 → Vec3) = v := by
      rw [Module.Basis.coe_toOrthonormalBasis, hBv]
    have he_expr : e = ‖A0‖ / (mp.m * gp.mu) := by
      simpa [e, A0, z0] using hedef
    have hl_expr : l = ‖L0‖ ^ (2 : Nat) / (mp.m * gp.mu) := by
      simpa [l, L0, z0] using hldef
    refine ⟨eA, eB, ?_, ?_, heA_unit, heB_unit, heA_eB, hfocus, ?_⟩
    · dsimp [eA]
      rw [real_inner_smul_right, hLA0]
      ring
    · have hL0_norm_pos : 0 < ‖L0‖ := norm_pos_iff.mpr (by simpa [L0, z0] using hL)
      have hcoeff_nonzero : (1 / ‖L0‖ : Real) ≠ 0 := by
        exact ne_of_gt (by positivity : 0 < (1 / ‖L0‖ : Real))
      have hscaled : (1 / ‖L0‖ : Real) * inner ℝ L0 eB = 0 := by
        dsimp [eL] at heL_eB
        simpa [real_inner_smul_left] using heL_eB
      rcases mul_eq_zero.mp hscaled with hcoeff | hinner
      · exact False.elim (hcoeff_nonzero hcoeff)
      · exact hinner
    · intro t
      let q : Vec3 := (gamma t).1
      let x : Real := inner ℝ eA q
      let y : Real := inner ℝ eB q
      let r : Real := radialDist q
      have heL_q : inner ℝ eL q = 0 := by
        have hplane_t : inner ℝ L0 q = 0 := by
          simpa [L0, q, z0] using hplane t
        dsimp [eL]
        rw [real_inner_smul_left]
        rw [hplane_t]
        ring
      have hsum := oB.sum_repr' q
      have hqdecomp : q = x • eA + y • eB := by
        have hsum' :
            (inner ℝ eA q) • eA + (inner ℝ eB q) • eB + (inner ℝ eL q) • eL = q := by
          simpa [hoBv, v, Fin.sum_univ_three] using hsum
        calc
          q =
              (inner ℝ eA q) • eA + (inner ℝ eB q) • eB +
                (inner ℝ eL q) • eL := by
                  simpa using hsum'.symm
          _ = x • eA + y • eB := by
                simp [x, y, heL_q]
      have hr_sq : r ^ (2 : Nat) = x ^ (2 : Nat) + y ^ (2 : Nat) := by
        have hxy_orth : inner ℝ (x • eA) (y • eB) = 0 := by
          rw [real_inner_smul_left, real_inner_smul_right, heA_eB]
          ring
        have heA_norm : ‖eA‖ = 1 := by
          have hsquare : ‖eA‖ ^ (2 : Nat) = 1 := by
            simpa [real_inner_self_eq_norm_sq] using heA_unit
          have hsquare' : ‖eA‖ ^ (2 : Nat) = 1 ^ (2 : Nat) := by simpa using hsquare
          rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquare' with hnorm | hnorm
          · exact hnorm
          · have hnonneg : 0 ≤ ‖eA‖ := norm_nonneg eA
            linarith
        have heB_norm : ‖eB‖ = 1 := by
          have hsquare : ‖eB‖ ^ (2 : Nat) = 1 := by
            simpa [real_inner_self_eq_norm_sq] using heB_unit
          have hsquare' : ‖eB‖ ^ (2 : Nat) = 1 ^ (2 : Nat) := by simpa using hsquare
          rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquare' with hnorm | hnorm
          · exact hnorm
          · have hnonneg : 0 ≤ ‖eB‖ := norm_nonneg eB
            linarith
        have hxeA_sq : ‖x • eA‖ ^ (2 : Nat) = x ^ (2 : Nat) := by
          rw [norm_smul, heA_norm, mul_one]
          simp
        have hyeB_sq : ‖y • eB‖ ^ (2 : Nat) = y ^ (2 : Nat) := by
          rw [norm_smul, heB_norm, mul_one]
          simp
        calc
          r ^ (2 : Nat) = ‖q‖ ^ (2 : Nat) := by
            dsimp [r]
            simp [radialDist]
          _ = ‖x • eA + y • eB‖ ^ (2 : Nat) := by rw [hqdecomp]
          _ = ‖x • eA‖ ^ (2 : Nat) + ‖y • eB‖ ^ (2 : Nat) := by
                simpa [pow_two] using
                  norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (x • eA) (y • eB) hxy_orth
          _ = x ^ (2 : Nat) + y ^ (2 : Nat) := by rw [hxeA_sq, hyeB_sq]
      have hAeq : A0 = ‖A0‖ • eA := by
        dsimp [eA]
        calc
          A0 = (1 : Real) • A0 := by simp
          _ = (‖A0‖ * (1 / ‖A0‖)) • A0 := by
                congr 1
                field_simp [hA0norm]
          _ = ‖A0‖ • eA := by rw [smul_smul]
      have hcoeff :
          inner ℝ A0 q = ‖L0‖ ^ (2 : Nat) - (mp.m * gp.mu) * r := by
        dsimp [A0, L0, q, r, z0]
        exact (kepler_first_law mp gp gamma hgamma t).1
      have hA_inner : inner ℝ A0 q = ‖A0‖ * x := by
        dsimp [x, eA]
        rw [real_inner_smul_left]
        field_simp [hA0norm]
      have hscale : (mp.m * gp.mu) * e = ‖A0‖ := by
        rw [he_expr, div_eq_mul_inv]
        calc
          (mp.m * gp.mu) * (‖A0‖ * (mp.m * gp.mu)⁻¹)
              = ‖A0‖ * ((mp.m * gp.mu) * (mp.m * gp.mu)⁻¹) := by ring
          _ = ‖A0‖ * 1 := by rw [mul_inv_cancel₀ hmμ]
          _ = ‖A0‖ := by ring
      have hlscale : (mp.m * gp.mu) * l = ‖L0‖ ^ (2 : Nat) := by
        rw [hl_expr, div_eq_mul_inv]
        calc
          (mp.m * gp.mu) * (‖L0‖ ^ (2 : Nat) * (mp.m * gp.mu)⁻¹)
              = ‖L0‖ ^ (2 : Nat) * ((mp.m * gp.mu) * (mp.m * gp.mu)⁻¹) := by ring
          _ = ‖L0‖ ^ (2 : Nat) * 1 := by rw [mul_inv_cancel₀ hmμ]
          _ = ‖L0‖ ^ (2 : Nat) := by ring
      have hline_mul :
          (mp.m * gp.mu) * (r + e * x) = (mp.m * gp.mu) * l := by
        calc
          (mp.m * gp.mu) * (r + e * x)
              = (mp.m * gp.mu) * r + ((mp.m * gp.mu) * e) * x := by ring
          _ = (mp.m * gp.mu) * r + ‖A0‖ * x := by rw [hscale]
          _ = (mp.m * gp.mu) * r + inner ℝ A0 q := by rw [hA_inner]
          _ = ‖L0‖ ^ (2 : Nat) := by linarith [hcoeff]
          _ = (mp.m * gp.mu) * l := by simpa using hlscale.symm
      have hline : r + e * x = l := by
        exact mul_left_cancel₀ hmμ hline_mul
      have ha0 : a ≠ 0 := ne_of_gt ha
      have hb0 : b ≠ 0 := ne_of_gt hb
      have hline' : r = l - e * x := by
        linarith [hline]
      have hcurve_eq :
          x ^ (2 : Nat) + y ^ (2 : Nat) =
            l ^ (2 : Nat) - 2 * l * e * x + e ^ (2 : Nat) * x ^ (2 : Nat) := by
        calc
          x ^ (2 : Nat) + y ^ (2 : Nat) = r ^ (2 : Nat) := by symm; exact hr_sq
          _ = (l - e * x) ^ (2 : Nat) := by rw [hline']
          _ = l ^ (2 : Nat) - 2 * l * e * x + e ^ (2 : Nat) * x ^ (2 : Nat) := by ring
      have hl' : l = a - a * e ^ (2 : Nat) := by
        calc
          l = a * (1 - e ^ (2 : Nat)) := hl
          _ = a - a * e ^ (2 : Nat) := by ring
      have hpoly1 :
          b ^ (2 : Nat) * x ^ (2 : Nat) +
              2 * a * e * b ^ (2 : Nat) * x +
              a ^ (2 : Nat) * y ^ (2 : Nat) =
            b ^ (2 : Nat) * b ^ (2 : Nat) := by
        exact ellipse_poly1 a b e l x y hcurve_eq hl hb_sq
      have hpoly :
          b ^ (2 : Nat) * (x + a * e) ^ (2 : Nat) + a ^ (2 : Nat) * y ^ (2 : Nat) =
            a ^ (2 : Nat) * b ^ (2 : Nat) := by
        exact ellipse_poly2 a b e x y hpoly1 hfocus
      have hcart :
          ((x + a * e) ^ (2 : Nat)) / (a ^ (2 : Nat)) +
              (y ^ (2 : Nat)) / (b ^ (2 : Nat)) =
            1 := by
        exact ellipse_cartesian_from_poly a b e x y ha0 hb0 hpoly
      simpa [q, x, y]

theorem kepler_first_law_normalized_circle
    (mp : MassParam) (gp : GravitationalParam) (gamma : Real -> PhaseSpace)
    (hgamma : IsSolution mp gp gamma) (hE : energy mp gp (gamma 0) < 0)
    (hL : angularMomentum (gamma 0) ≠ 0) :
    let z0 := gamma 0
    let A0 := laplaceLenz mp gp z0
    let L0 := angularMomentum z0
    let e := eccentricity mp gp z0
    let a := semiMajorAxis mp gp z0
    let b := semiMinorAxis mp gp z0
    A0 ≠ 0 →
      ∃ eA eB : Vec3,
        inner ℝ L0 eA = 0 ∧
        inner ℝ L0 eB = 0 ∧
        inner ℝ eA eA = 1 ∧
        inner ℝ eB eB = 1 ∧
        inner ℝ eA eB = 0 ∧
        ∀ t : Real,
          let q := (gamma t).1
          let u := (inner ℝ eA q + a * e) / a
          let v := inner ℝ eB q / b
          u ^ (2 : Nat) + v ^ (2 : Nat) = 1 := by
  dsimp
  set z0 : PhaseSpace := gamma 0
  set A0 : Vec3 := laplaceLenz mp gp z0
  set L0 : Vec3 := angularMomentum z0
  set e : Real := eccentricity mp gp z0
  set a : Real := semiMajorAxis mp gp z0
  set b : Real := semiMinorAxis mp gp z0
  intro hA0
  rcases kepler_first_law_cartesian_ellipse mp gp gamma hgamma hE hL |>.2 hA0 with
    ⟨eA, eB, hLeA, hLeB, heA, heB, heAeB, _hfocus, hcurve⟩
  refine ⟨eA, eB, hLeA, hLeB, heA, heB, heAeB, ?_⟩
  intro t
  let q : Vec3 := (gamma t).1
  let x : Real := inner ℝ eA q
  let y : Real := inner ℝ eB q
  let u : Real := (x + a * e) / a
  let v : Real := y / b
  have ha0 : a ≠ 0 := ne_of_gt (semi_major_axis mp gp z0 hE)
  have hb0 : b ≠ 0 := ne_of_gt (semiMinorAxis_pos mp gp z0 hE hL (hgamma.noCollision 0))
  have hcart := hcurve t
  have hu :
      ((x + a * e) ^ (2 : Nat)) / (a ^ (2 : Nat)) = u ^ (2 : Nat) := by
    dsimp [u]
    field_simp [ha0]
  have hv :
      y ^ (2 : Nat) / (b ^ (2 : Nat)) = v ^ (2 : Nat) := by
    dsimp [v]
    field_simp [hb0]
  calc
    u ^ (2 : Nat) + v ^ (2 : Nat)
        = ((x + a * e) ^ (2 : Nat)) / (a ^ (2 : Nat)) + y ^ (2 : Nat) / (b ^ (2 : Nat)) := by
            rw [← hu, ← hv]
    _ = 1 := by simpa [q, x, y] using hcart

theorem kepler_planarity_theorem
    (mp : MassParam) (gp : GravitationalParam) (gamma : Real -> PhaseSpace)
    (hgamma : IsSolution mp gp gamma) (hL : angularMomentum (gamma 0) ≠ 0) :
    let L0 := angularMomentum (gamma 0)
    ∀ t : Real, (gamma t).1 ∈ { y : Vec3 | inner ℝ L0 y = 0 } := by
  dsimp
  intro t
  simpa using (planarity mp gp gamma hgamma hL t).1

theorem kepler_first_law_focus_geometry
    (mp : MassParam) (gp : GravitationalParam) (gamma : Real -> PhaseSpace)
    (hgamma : IsSolution mp gp gamma) (hE : energy mp gp (gamma 0) < 0)
    (hL : angularMomentum (gamma 0) ≠ 0) :
    let z0 := gamma 0
    let A0 := laplaceLenz mp gp z0
    let L0 := angularMomentum z0
    let e := eccentricity mp gp z0
    let a := semiMajorAxis mp gp z0
    let b := semiMinorAxis mp gp z0
    A0 ≠ 0 →
      ∃ eA eB : Vec3,
        inner ℝ L0 eA = 0 ∧
        inner ℝ L0 eB = 0 ∧
        inner ℝ eA eA = 1 ∧
        inner ℝ eB eB = 1 ∧
        inner ℝ eA eB = 0 ∧
        Real.sqrt (a ^ (2 : Nat) - b ^ (2 : Nat)) = a * e ∧
        (-a * e) + Real.sqrt (a ^ (2 : Nat) - b ^ (2 : Nat)) = 0 ∧
        (-a * e) - Real.sqrt (a ^ (2 : Nat) - b ^ (2 : Nat)) = -2 * a * e ∧
        ∀ t : Real,
          let q := (gamma t).1
          let x := inner ℝ eA q
          let y := inner ℝ eB q
          ((x + a * e) ^ (2 : Nat)) / (a ^ (2 : Nat)) +
              (y ^ (2 : Nat)) / (b ^ (2 : Nat)) =
            1 := by
  dsimp
  set z0 : PhaseSpace := gamma 0
  set A0 : Vec3 := laplaceLenz mp gp z0
  set L0 : Vec3 := angularMomentum z0
  set e : Real := eccentricity mp gp z0
  set a : Real := semiMajorAxis mp gp z0
  set b : Real := semiMinorAxis mp gp z0
  intro hA0
  have hcart := kepler_first_law_cartesian_ellipse mp gp gamma hgamma hE hL
  rcases hcart.2 hA0 with ⟨eA, eB, hLeA, hLeB, heA, heB, heAeB, hfocus, hcurve⟩
  have hnonneg_ae : 0 ≤ a * e := by
    have ha : 0 < a := by
      simpa [a, z0] using semi_major_axis mp gp z0 hE
    have he0 : 0 ≤ e := by
      simpa [e, z0] using eccentricity_nonneg mp gp z0
    exact mul_nonneg (le_of_lt ha) he0
  have hsqrt :
      Real.sqrt (a ^ (2 : Nat) - b ^ (2 : Nat)) = a * e := by
    rw [hfocus, Real.sqrt_sq_eq_abs, abs_of_nonneg hnonneg_ae]
  refine ⟨eA, eB, hLeA, hLeB, heA, heB, heAeB, hsqrt, ?_, ?_, hcurve⟩
  · nlinarith [hsqrt]
  · nlinarith [hsqrt]

theorem kepler_first_law_origin_is_focus
    (mp : MassParam) (gp : GravitationalParam) (gamma : Real -> PhaseSpace)
    (hgamma : IsSolution mp gp gamma) (hE : energy mp gp (gamma 0) < 0)
    (hL : angularMomentum (gamma 0) ≠ 0) :
    let z0 := gamma 0
    let A0 := laplaceLenz mp gp z0
    let L0 := angularMomentum z0
    let e := eccentricity mp gp z0
    let a := semiMajorAxis mp gp z0
    let b := semiMinorAxis mp gp z0
    A0 ≠ 0 →
      ∃ eA eB : Vec3,
        inner ℝ L0 eA = 0 ∧
        inner ℝ L0 eB = 0 ∧
        inner ℝ eA eA = 1 ∧
        inner ℝ eB eB = 1 ∧
        inner ℝ eA eB = 0 ∧
        Real.sqrt (a ^ (2 : Nat) - b ^ (2 : Nat)) = a * e ∧
        ((0 : Real) = (-a * e) + Real.sqrt (a ^ (2 : Nat) - b ^ (2 : Nat))) ∧
        (((-2 * a * e : Real)) = (-a * e) - Real.sqrt (a ^ (2 : Nat) - b ^ (2 : Nat))) := by
  dsimp
  set z0 : PhaseSpace := gamma 0
  set A0 : Vec3 := laplaceLenz mp gp z0
  set L0 : Vec3 := angularMomentum z0
  set e : Real := eccentricity mp gp z0
  set a : Real := semiMajorAxis mp gp z0
  set b : Real := semiMinorAxis mp gp z0
  intro hA0
  rcases kepler_first_law_focus_geometry mp gp gamma hgamma hE hL hA0 with
    ⟨eA, eB, hLeA, hLeB, heA, heB, heAeB, hsqrt, hfocus0, hfocus1, _hcurve⟩
  refine ⟨eA, eB, hLeA, hLeB, heA, heB, heAeB, hsqrt, ?_, ?_⟩
  · linarith [hfocus0]
  · linarith [hfocus1]

theorem kepler_first_law_source
    (mp : MassParam) (gp : GravitationalParam) (gamma : Real -> PhaseSpace)
    (hgamma : IsSolution mp gp gamma) (hE : energy mp gp (gamma 0) < 0)
    (hL : angularMomentum (gamma 0) ≠ 0) :
    let z0 := gamma 0
    let A0 := laplaceLenz mp gp z0
    let L0 := angularMomentum z0
    let e := eccentricity mp gp z0
    let l := semiLatusRectum mp gp z0
    let a := semiMajorAxis mp gp z0
    let b := semiMinorAxis mp gp z0
    (∀ t : Real, inner ℝ L0 (gamma t).1 = 0) ∧
      e = ‖A0‖ / (mp.m * gp.mu) ∧
      l = ‖L0‖ ^ (2 : Nat) / (mp.m * gp.mu) ∧
      a = -(gp.mu / (2 * energy mp gp z0)) ∧
      0 ≤ e ∧ e < 1 ∧ 0 < a ∧ 0 < b ∧
      (A0 = 0 → ∀ t : Real, radialDist (gamma t).1 = a) ∧
      (A0 ≠ 0 →
        ∃ eA eB : Vec3,
          inner ℝ L0 eA = 0 ∧
          inner ℝ L0 eB = 0 ∧
          inner ℝ eA eA = 1 ∧
          inner ℝ eB eB = 1 ∧
          inner ℝ eA eB = 0 ∧
          Real.sqrt (a ^ (2 : Nat) - b ^ (2 : Nat)) = a * e ∧
          (-a * e) + Real.sqrt (a ^ (2 : Nat) - b ^ (2 : Nat)) = 0 ∧
          (-a * e) - Real.sqrt (a ^ (2 : Nat) - b ^ (2 : Nat)) = -2 * a * e ∧
          ∀ t : Real,
            let q := (gamma t).1
            let x := inner ℝ eA q
            let y := inner ℝ eB q
            ((x + a * e) ^ (2 : Nat)) / (a ^ (2 : Nat)) +
                (y ^ (2 : Nat)) / (b ^ (2 : Nat)) =
              1) := by
  dsimp
  set z0 : PhaseSpace := gamma 0
  set A0 : Vec3 := laplaceLenz mp gp z0
  set L0 : Vec3 := angularMomentum z0
  set e : Real := eccentricity mp gp z0
  set l : Real := semiLatusRectum mp gp z0
  set a : Real := semiMajorAxis mp gp z0
  set b : Real := semiMinorAxis mp gp z0
  have hexact := kepler_first_law_exact mp gp gamma hgamma hE hL
  rcases hexact with ⟨hplane, hedef, hldef, hadef, he0, he1, ha, hb, _hl, _hb, hcircle, _horbit⟩
  refine ⟨hplane, hedef, hldef, hadef, he0, he1, ha, hb, ?_, ?_⟩
  · intro hA0 t
    have hcart := kepler_first_law_cartesian_ellipse mp gp gamma hgamma hE hL
    exact (hcart.1 hA0 t).1
  · intro hA0
    simpa [z0, A0, L0, e, a, b] using
      kepler_first_law_focus_geometry mp gp gamma hgamma hE hL hA0

lemma sweptAreaOn_eq_interval_mul_areal_velocity
    (mp : MassParam) (gp : GravitationalParam) (gamma : Real -> PhaseSpace)
    (hgamma : IsSolution mp gp gamma) (hL : angularMomentum (gamma 0) ≠ 0)
    (t0 t1 : Real) :
    sweptAreaOn mp gamma t0 t1 =
      (t1 - t0) * (‖angularMomentum (gamma 0)‖ / (2 * mp.m)) := by
  unfold sweptAreaOn
  have hconst := kepler_second_law mp gp gamma hgamma hL
  rw [show (fun τ : Real => signedArealVelocity mp gamma τ) =
      fun _ : Real => ‖angularMomentum (gamma 0)‖ / (2 * mp.m) by
        funext τ
        exact hconst τ]
  rw [intervalIntegral.integral_const]
  simp [smul_eq_mul, sub_eq_add_neg, mul_comm]

theorem equal_areas_in_equal_times
    (mp : MassParam) (gp : GravitationalParam) (gamma : Real -> PhaseSpace)
    (hgamma : IsSolution mp gp gamma) (hL : angularMomentum (gamma 0) ≠ 0)
    {t0 t1 s0 s1 : Real} (hspan : t1 - t0 = s1 - s0) :
    sweptAreaOn mp gamma t0 t1 = sweptAreaOn mp gamma s0 s1 := by
  rw [sweptAreaOn_eq_interval_mul_areal_velocity mp gp gamma hgamma hL t0 t1,
    sweptAreaOn_eq_interval_mul_areal_velocity mp gp gamma hgamma hL s0 s1,
    hspan]

theorem kepler_second_law_source
    (mp : MassParam) (gp : GravitationalParam) (gamma : Real -> PhaseSpace)
    (hgamma : IsSolution mp gp gamma) (hL : angularMomentum (gamma 0) ≠ 0) :
    (∀ t : Real,
      signedArealVelocity mp gamma t =
        ‖angularMomentum (gamma 0)‖ / (2 * mp.m)) ∧
    (∀ {t0 t1 s0 s1 : Real}, t1 - t0 = s1 - s0 →
      sweptAreaOn mp gamma t0 t1 = sweptAreaOn mp gamma s0 s1) := by
  exact ⟨kepler_second_law mp gp gamma hgamma hL,
    by
      intro t0 t1 s0 s1 hspan
      exact equal_areas_in_equal_times mp gp gamma hgamma hL hspan⟩

theorem signedArealVelocity_pos
    (mp : MassParam) (gp : GravitationalParam) (gamma : Real -> PhaseSpace)
    (hgamma : IsSolution mp gp gamma) (hL : angularMomentum (gamma 0) ≠ 0) :
    ∀ t : Real, 0 < signedArealVelocity mp gamma t := by
  intro t
  rw [kepler_second_law mp gp gamma hgamma hL t]
  exact div_pos (norm_pos_iff.mpr hL) (by nlinarith [mp.hm])

theorem sweptAreaOn_nonneg_of_le
    (mp : MassParam) (gp : GravitationalParam) (gamma : Real -> PhaseSpace)
    (hgamma : IsSolution mp gp gamma) (hL : angularMomentum (gamma 0) ≠ 0)
    {t0 t1 : Real} (hle : t0 ≤ t1) :
    0 ≤ sweptAreaOn mp gamma t0 t1 := by
  rw [sweptAreaOn_eq_interval_mul_areal_velocity mp gp gamma hgamma hL t0 t1]
  apply mul_nonneg
  · exact sub_nonneg.mpr hle
  · exact le_of_lt (div_pos (norm_pos_iff.mpr hL) (by nlinarith [mp.hm]))

theorem sweptAreaOn_pos_of_lt
    (mp : MassParam) (gp : GravitationalParam) (gamma : Real -> PhaseSpace)
    (hgamma : IsSolution mp gp gamma) (hL : angularMomentum (gamma 0) ≠ 0)
    {t0 t1 : Real} (hlt : t0 < t1) :
    0 < sweptAreaOn mp gamma t0 t1 := by
  rw [sweptAreaOn_eq_interval_mul_areal_velocity mp gp gamma hgamma hL t0 t1]
  apply mul_pos
  · exact sub_pos.mpr hlt
  · exact div_pos (norm_pos_iff.mpr hL) (by nlinarith [mp.hm])

theorem configurationPeriod_sweptArea_pos
    (mp : MassParam) (gp : GravitationalParam) (gamma : Real -> PhaseSpace)
    (hgamma : IsSolution mp gp gamma) (hL : angularMomentum (gamma 0) ≠ 0)
    {T : Real} (hT : HasConfigurationPeriod mp gp gamma T) :
    0 < sweptAreaOn mp gamma 0 T := by
  simpa using sweptAreaOn_pos_of_lt mp gp gamma hgamma hL hT.pos

lemma unitCircle_point_exists_angle
    (u v : Real) (h : u ^ (2 : Nat) + v ^ (2 : Nat) = 1) :
    ∃ θ : Real, u = Real.cos θ ∧ v = Real.sin θ := by
  have hu_le : u ^ (2 : Nat) ≤ 1 := by
    nlinarith [sq_nonneg v]
  have hu_lower : -1 ≤ u := by
    nlinarith [hu_le, sq_nonneg u]
  have hu_upper : u ≤ 1 := by
    nlinarith [hu_le, sq_nonneg u]
  by_cases hv : 0 ≤ v
  · refine ⟨Real.arccos u, ?_, ?_⟩
    · symm
      exact Real.cos_arccos hu_lower hu_upper
    · rw [Real.sin_arccos]
      have hnonneg : 0 ≤ 1 - u ^ (2 : Nat) := by
        nlinarith [sq_nonneg v, h]
      have hsqrt_sq : (Real.sqrt (1 - u ^ (2 : Nat))) ^ (2 : Nat) = v ^ (2 : Nat) := by
        rw [Real.sq_sqrt hnonneg]
        nlinarith [h]
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsqrt_sq with hEq | hEq
      · exact hEq.symm
      · linarith [Real.sqrt_nonneg (1 - u ^ (2 : Nat)), hv, hEq]
  · have hnegv : 0 ≤ -v := by
      linarith
    refine ⟨-Real.arccos u, ?_, ?_⟩
    · rw [Real.cos_neg, Real.cos_arccos hu_lower hu_upper]
    · rw [Real.sin_neg, Real.sin_arccos]
      have hnonneg : 0 ≤ 1 - u ^ (2 : Nat) := by
        nlinarith [sq_nonneg v, h]
      have hsqrt_sq : (Real.sqrt (1 - u ^ (2 : Nat))) ^ (2 : Nat) = (-v) ^ (2 : Nat) := by
        rw [Real.sq_sqrt hnonneg]
        nlinarith [h]
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsqrt_sq with hEq | hEq
      · linarith
      · linarith [Real.sqrt_nonneg (1 - u ^ (2 : Nat)), hnegv, hEq]

lemma standardEllipse_point_exists_angle
    (a b e x y : Real) (ha : 0 < a) (hb : 0 < b)
    (hxy :
      ((x + a * e) ^ (2 : Nat)) / (a ^ (2 : Nat)) +
        (y ^ (2 : Nat)) / (b ^ (2 : Nat)) = 1) :
    ∃ θ : Real, x = a * (Real.cos θ - e) ∧ y = b * Real.sin θ := by
  let u : Real := (x + a * e) / a
  let v : Real := y / b
  have huv : u ^ (2 : Nat) + v ^ (2 : Nat) = 1 := by
    dsimp [u, v]
    have ha0 : a ≠ 0 := ne_of_gt ha
    have hb0 : b ≠ 0 := ne_of_gt hb
    field_simp [ha0, hb0] at hxy ⊢
    nlinarith
  rcases unitCircle_point_exists_angle u v huv with ⟨θ, hu, hv⟩
  refine ⟨θ, ?_, ?_⟩
  · dsimp [u] at hu
    have hmul : x + a * e = Real.cos θ * a := (div_eq_iff (ne_of_gt ha)).1 hu
    nlinarith
  · dsimp [v] at hv
    have hmul : y = Real.sin θ * b := (div_eq_iff (ne_of_gt hb)).1 hv
    nlinarith [hmul]

lemma curve_on_standardEllipse_exists_angle
    (gamma : Real -> PhaseSpace) (eA eB : Vec3) (a b e : Real)
    (ha : 0 < a) (hb : 0 < b)
    (hcurve :
      ∀ t : Real,
        let q := (gamma t).1
        let x := inner ℝ eA q
        let y := inner ℝ eB q
        ((x + a * e) ^ (2 : Nat)) / (a ^ (2 : Nat)) +
            (y ^ (2 : Nat)) / (b ^ (2 : Nat)) =
          1) :
    ∀ t : Real,
      ∃ θ : Real,
        inner ℝ eA (gamma t).1 = a * (Real.cos θ - e) ∧
          inner ℝ eB (gamma t).1 = b * Real.sin θ := by
  intro t
  let x : Real := inner ℝ eA (gamma t).1
  let y : Real := inner ℝ eB (gamma t).1
  have hxy :
      ((x + a * e) ^ (2 : Nat)) / (a ^ (2 : Nat)) +
          (y ^ (2 : Nat)) / (b ^ (2 : Nat)) =
        1 := by
    simpa [x, y] using hcurve t
  rcases standardEllipse_point_exists_angle a b e x y ha hb hxy with ⟨θ, hx, hy⟩
  exact ⟨θ, by simpa [x] using hx, by simpa [y] using hy⟩

theorem kepler_first_law_exists_standardEllipse_angle
    (mp : MassParam) (gp : GravitationalParam) (gamma : Real -> PhaseSpace)
    (hgamma : IsSolution mp gp gamma) (hE : energy mp gp (gamma 0) < 0)
    (hL : angularMomentum (gamma 0) ≠ 0) :
    let z0 := gamma 0
    let A0 := laplaceLenz mp gp z0
    let L0 := angularMomentum z0
    let e := eccentricity mp gp z0
    let a := semiMajorAxis mp gp z0
    let b := semiMinorAxis mp gp z0
    A0 ≠ 0 →
      ∃ eA eB : Vec3,
        inner ℝ L0 eA = 0 ∧
        inner ℝ L0 eB = 0 ∧
        inner ℝ eA eA = 1 ∧
        inner ℝ eB eB = 1 ∧
        inner ℝ eA eB = 0 ∧
        ∀ t : Real,
          ∃ θ : Real,
            inner ℝ eA (gamma t).1 = a * (Real.cos θ - e) ∧
              inner ℝ eB (gamma t).1 = b * Real.sin θ := by
  dsimp
  set z0 : PhaseSpace := gamma 0
  set A0 : Vec3 := laplaceLenz mp gp z0
  set L0 : Vec3 := angularMomentum z0
  set e : Real := eccentricity mp gp z0
  set a : Real := semiMajorAxis mp gp z0
  set b : Real := semiMinorAxis mp gp z0
  intro hA0
  rcases kepler_first_law_cartesian_ellipse mp gp gamma hgamma hE hL |>.2 hA0 with
    ⟨eA, eB, hLeA, hLeB, heA, heB, heAeB, _hfocus, hcurve⟩
  refine ⟨eA, eB, hLeA, hLeB, heA, heB, heAeB, ?_⟩
  have ha : 0 < a := semi_major_axis mp gp z0 hE
  have hb : 0 < b := semiMinorAxis_pos mp gp z0 hE hL (hgamma.noCollision 0)
  exact curve_on_standardEllipse_exists_angle gamma eA eB a b e ha hb hcurve

set_option maxHeartbeats 800000 in
-- Complex nonlinear arithmetic + trig identities for ellipse parametrization (unit circle lemma).
-- Required for configurationPeriod_sweptArea_eq_pi_mul_semiAxes (GS Ch. I §5 geometry).
lemma unitCircle_eq_cos_sin_of_hasDerivAt
    {u v θ omega : Real → Real}
    (hu : ∀ t : Real, HasDerivAt u (-omega t * v t) t)
    (hv : ∀ t : Real, HasDerivAt v (omega t * u t) t)
    (hθ : ∀ t : Real, HasDerivAt θ (omega t) t)
    (h0u : u 0 = Real.cos (θ 0))
    (h0v : v 0 = Real.sin (θ 0)) :
    ∀ t : Real, u t = Real.cos (θ t) ∧ v t = Real.sin (θ t) := by
  let d : Real → Real := fun t =>
    (u t - Real.cos (θ t)) * (u t - Real.cos (θ t)) +
      (v t - Real.sin (θ t)) * (v t - Real.sin (θ t))
  have hd : ∀ t : Real, HasDerivAt d 0 t := by
    intro t
    have hucos : HasDerivAt (fun s : Real => u s - Real.cos (θ s))
        (-omega t * v t + Real.sin (θ t) * omega t) t := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_assoc, mul_left_comm, mul_comm]
        using (hu t).sub ((Real.hasDerivAt_cos (θ t)).comp t (hθ t))
    have hvsin : HasDerivAt (fun s : Real => v s - Real.sin (θ s))
        (omega t * u t - Real.cos (θ t) * omega t) t := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_assoc, mul_left_comm, mul_comm]
        using (hv t).sub ((Real.hasDerivAt_sin (θ t)).comp t (hθ t))
    have hd' : HasDerivAt d
        (2 * (u t - Real.cos (θ t)) * (-omega t * v t + Real.sin (θ t) * omega t) +
          2 * (v t - Real.sin (θ t)) * (omega t * u t - Real.cos (θ t) * omega t)) t := by
      convert (hucos.mul hucos).add (hvsin.mul hvsin) using 1;
        simp only [mul_add, add_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
          mul_assoc, mul_left_comm, mul_comm]; ring
    have hzero :
        2 * (u t - Real.cos (θ t)) * (-omega t * v t + Real.sin (θ t) * omega t) +
          2 * (v t - Real.sin (θ t)) * (omega t * u t - Real.cos (θ t) * omega t) = 0 := by
      ring
    convert hd' using 1
    exact hzero.symm
  have hdiff : Differentiable ℝ d := fun t => (hd t).differentiableAt
  have hconst : ∀ t : Real, d t = d 0 := fun t =>
    is_const_of_deriv_eq_zero hdiff (fun s => by simpa using (hd s).deriv) t 0
  intro t
  have hd0 : d 0 = 0 := by
    simp [d, h0u, h0v]
  have hdt : d t = 0 := by
    rw [hconst t, hd0]
  have hdt' :
      (u t - Real.cos (θ t)) * (u t - Real.cos (θ t)) +
        (v t - Real.sin (θ t)) * (v t - Real.sin (θ t)) = 0 := by
    simpa [d] using hdt
  have hsum_nonneg :
      0 ≤ (u t - Real.cos (θ t)) * (u t - Real.cos (θ t)) ∧
        0 ≤ (v t - Real.sin (θ t)) * (v t - Real.sin (θ t)) := by
    constructor <;> nlinarith [sq_nonneg (u t - Real.cos (θ t)), sq_nonneg (v t - Real.sin (θ t))]
  have hu_eq : u t - Real.cos (θ t) = 0 := by
    nlinarith [hdt', hsum_nonneg.1, hsum_nonneg.2]
  have hv_eq : v t - Real.sin (θ t) = 0 := by
    nlinarith [hdt', hsum_nonneg.1, hsum_nonneg.2]
  exact ⟨sub_eq_zero.mp hu_eq, sub_eq_zero.mp hv_eq⟩

set_option maxHeartbeats 800000 in
-- Heavy nlinarith/ring in oriented ellipse lemma for full Kepler first law (GS Ch. I §5).
theorem kepler_first_law_oriented_standardEllipse
    (mp : MassParam) (gp : GravitationalParam) (gamma : Real -> PhaseSpace)
    (hgamma : IsSolution mp gp gamma) (hE : energy mp gp (gamma 0) < 0)
    (hL : angularMomentum (gamma 0) ≠ 0) :
    let z0 := gamma 0
    let L0 := angularMomentum z0
    let e := eccentricity mp gp z0
    let a := semiMajorAxis mp gp z0
    let b := semiMinorAxis mp gp z0
    let eL := (1 / ‖L0‖) • L0
    ∃ eA eB : Vec3,
      inner ℝ L0 eA = 0 ∧
      inner ℝ L0 eB = 0 ∧
      inner ℝ eA eA = 1 ∧
      inner ℝ eB eB = 1 ∧
      inner ℝ eA eB = 0 ∧
      inner ℝ eL (cross eA eB) = 1 ∧
      ∀ t : Real,
        let q := (gamma t).1
        let x := inner ℝ eA q
        let y := inner ℝ eB q
        ((x + a * e) ^ (2 : Nat)) / (a ^ (2 : Nat)) +
            (y ^ (2 : Nat)) / (b ^ (2 : Nat)) =
          1 := by
  dsimp
  set z0 : PhaseSpace := gamma 0
  set A0 : Vec3 := laplaceLenz mp gp z0
  set L0 : Vec3 := angularMomentum z0
  set e : Real := eccentricity mp gp z0
  set a : Real := semiMajorAxis mp gp z0
  set b : Real := semiMinorAxis mp gp z0
  let eL : Vec3 := (1 / ‖L0‖) • L0
  have hL0norm : ‖L0‖ ≠ 0 := norm_ne_zero_iff.mpr (by simpa [L0, z0] using hL)
  by_cases hA0 : A0 = 0
  · let eA : Vec3 := (1 / radialDist z0.1) • z0.1
    let eB : Vec3 := cross eL eA
    have hz0r : radialDist z0.1 = a := by
      simpa [z0, A0, a] using (kepler_first_law_cartesian_ellipse mp gp gamma hgamma hE hL).1 hA0 0 |>.1
    have hz0r_ne : radialDist z0.1 ≠ 0 := by simpa [z0] using hgamma.noCollision 0
    have he0 : e = 0 := by simp [e, A0, z0, eccentricity, hA0]
    have hLeA : inner ℝ L0 eA = 0 := by
      have hzplane : inner ℝ L0 z0.1 = 0 := by
        simpa [L0, z0] using (planarity mp gp gamma hgamma hL 0).1
      dsimp [eA]
      rw [real_inner_smul_right]
      rw [hzplane]
      ring
    have heA_unit : inner ℝ eA eA = 1 := by
      have hnormz0 : ‖z0.1‖ ≠ 0 := by simpa [radialDist] using hz0r_ne
      dsimp [eA]
      rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, radialDist]
      field_simp [hnormz0]
    have heL_unit : inner ℝ eL eL = 1 := by
      dsimp [eL]
      rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp [hL0norm]
    have heL_eA : inner ℝ eL eA = 0 := by
      dsimp [eL]
      rw [real_inner_smul_left, hLeA]
      ring
    have hLeB : inner ℝ L0 eB = 0 := by
      have : inner ℝ eL eB = 0 := by
        dsimp [eB]
        simpa using inner_cross_left_zero eL eA
      dsimp [eL] at this
      rw [real_inner_smul_left] at this
      have hcoeff : (1 / ‖L0‖ : Real) ≠ 0 := by
        simpa [one_div] using inv_ne_zero hL0norm
      exact (mul_eq_zero.mp this).resolve_left hcoeff
    have heA_eB : inner ℝ eA eB = 0 := by
      dsimp [eB]
      simpa using inner_cross_right_zero eL eA
    have heB_unit : inner ℝ eB eB = 1 := by
      have hnorm_sq : ‖eB‖ ^ (2 : Nat) = 1 := by
        calc
          ‖eB‖ ^ (2 : Nat)
              = ‖eL‖ ^ (2 : Nat) * ‖eA‖ ^ (2 : Nat) - (inner ℝ eL eA) ^ (2 : Nat) := by
                  simpa [eB] using norm_cross_sq eL eA
          _ = 1 := by
                rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, heL_unit, heA_unit,
                  heL_eA]
                ring
      simpa [real_inner_self_eq_norm_sq] using hnorm_sq
    have horient : inner ℝ eL (cross eA eB) = 1 := by
      dsimp [eB]
      calc
        inner ℝ eL (cross eA (cross eL eA))
            = inner ℝ eL ((inner ℝ eA eA) • eL - (inner ℝ eL eA) • eA) := by
                rw [cross_cross_eq_inner]
        _ = inner ℝ eL eL := by
              rw [heA_unit, heL_eA]
              simp
        _ = 1 := heL_unit
    refine ⟨eA, eB, hLeA, hLeB, heA_unit, heB_unit, heA_eB, horient, ?_⟩
    intro t
    let q : Vec3 := (gamma t).1
    let x : Real := inner ℝ eA q
    let y : Real := inner ℝ eB q
    have hplane_t : inner ℝ L0 q = 0 := by
      simpa [L0, q, z0] using (planarity mp gp gamma hgamma hL t).1
    have hab : a = b := by
      simpa [z0, A0, a, b] using (kepler_first_law_cartesian_ellipse mp gp gamma hgamma hE hL).1 hA0 0 |>.2
    have hqdecomp : q = x • eA + y • eB := by
      apply position_eq_of_adapted_coords_eq L0 eA eB q (x • eA + y • eB)
      · simpa [z0, L0] using hL
      · exact hLeA
      · exact hLeB
      · exact heA_unit
      · exact heB_unit
      · exact heA_eB
      · exact hplane_t
      · have hxeA : inner ℝ L0 (x • eA) = 0 := by
          rw [real_inner_smul_right, hLeA]
          ring
        have hyeB : inner ℝ L0 (y • eB) = 0 := by
          rw [real_inner_smul_right, hLeB]
          ring
        calc
          inner ℝ L0 (x • eA + y • eB)
              = inner ℝ L0 (x • eA) + inner ℝ L0 (y • eB) := by
                  rw [inner_add_right]
          _ = 0 + 0 := by rw [hxeA, hyeB]
          _ = 0 := by ring
      · have heA_normsq : ‖eA‖ ^ (2 : Nat) = 1 := by
          simpa [real_inner_self_eq_norm_sq] using heA_unit
        have hxeA : inner ℝ eA (x • eA) = x := by
          rw [real_inner_smul_right, real_inner_self_eq_norm_sq, heA_normsq]
          ring
        have hyeB : inner ℝ eA (y • eB) = 0 := by
          rw [real_inner_smul_right, heA_eB]
          ring
        calc
          inner ℝ eA q = x := by simp [x]
          _ = x + 0 := by ring
          _ = inner ℝ eA (x • eA) + inner ℝ eA (y • eB) := by rw [hxeA, hyeB]
          _ = inner ℝ eA (x • eA + y • eB) := by rw [inner_add_right]
      · have heB_normsq : ‖eB‖ ^ (2 : Nat) = 1 := by
          simpa [real_inner_self_eq_norm_sq] using heB_unit
        have hxeA : inner ℝ eB (x • eA) = 0 := by
          rw [real_inner_smul_right, real_inner_comm, heA_eB]
          ring
        have hyeB : inner ℝ eB (y • eB) = y := by
          rw [real_inner_smul_right, real_inner_self_eq_norm_sq, heB_normsq]
          ring
        calc
          inner ℝ eB q = y := by simp [y]
          _ = 0 + y := by ring
          _ = inner ℝ eB (x • eA) + inner ℝ eB (y • eB) := by rw [hxeA, hyeB]
          _ = inner ℝ eB (x • eA + y • eB) := by rw [inner_add_right]
    have hr : radialDist q = a := by
      calc
        radialDist q = semiMajorAxis mp gp z0 := by
          simpa [q, z0, a, A0] using (kepler_first_law_cartesian_ellipse mp gp gamma hgamma hE hL).1 hA0 t |>.1
        _ = a := rfl
    have hr_sq : x ^ (2 : Nat) + y ^ (2 : Nat) = a ^ (2 : Nat) := by
      have hxy_orth : inner ℝ (x • eA) (y • eB) = 0 := by
        rw [real_inner_smul_left, real_inner_smul_right, heA_eB]
        ring
      have heA_norm : ‖eA‖ = 1 := by
        have : ‖eA‖ ^ (2 : Nat) = 1 := by simpa [real_inner_self_eq_norm_sq] using heA_unit
        nlinarith [norm_nonneg eA]
      have heB_norm : ‖eB‖ = 1 := by
        have : ‖eB‖ ^ (2 : Nat) = 1 := by simpa [real_inner_self_eq_norm_sq] using heB_unit
        nlinarith [norm_nonneg eB]
      calc
        x ^ (2 : Nat) + y ^ (2 : Nat)
            = ‖x • eA‖ ^ (2 : Nat) + ‖y • eB‖ ^ (2 : Nat) := by
                rw [norm_smul, heA_norm, mul_one, norm_smul, heB_norm, mul_one]
                simp
        _ = ‖x • eA + y • eB‖ ^ (2 : Nat) := by
              symm
              simpa [pow_two] using
                norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (x • eA) (y • eB) hxy_orth
        _ = radialDist q ^ (2 : Nat) := by rw [hqdecomp, radialDist]
        _ = a ^ (2 : Nat) := by rw [hr]
    have ha0 : a ≠ 0 := ne_of_gt (semi_major_axis mp gp z0 hE)
    have hb0 : b ≠ 0 := ne_of_gt (semiMinorAxis_pos mp gp z0 hE hL (hgamma.noCollision 0))
    calc
      ((x + a * e) ^ (2 : Nat)) / (a ^ (2 : Nat)) + (y ^ (2 : Nat)) / (b ^ (2 : Nat))
          = (x ^ (2 : Nat) + y ^ (2 : Nat)) / (a ^ (2 : Nat)) := by
              rw [he0, hab]
              field_simp [ha0]
              ring
      _ = 1 := by
            apply (div_eq_one_iff_eq (pow_ne_zero 2 ha0)).2
            exact hr_sq
  · rcases (kepler_first_law_cartesian_ellipse mp gp gamma hgamma hE hL).2 hA0 with
      ⟨eA0, eB0, hLeA0, hLeB0, heA0, heB0, heAeB0, _hfocus, hcurve0⟩
    let w : Vec3 := cross eA0 eB0
    let σ : Real := inner ℝ eL w
    have heL_unit : inner ℝ eL eL = 1 := by
      dsimp [eL]
      rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp [hL0norm]
    have heL_eA0 : inner ℝ eL eA0 = 0 := by
      dsimp [eL]
      rw [real_inner_smul_left, hLeA0]
      ring
    have heL_eB0 : inner ℝ eL eB0 = 0 := by
      dsimp [eL]
      rw [real_inner_smul_left, hLeB0]
      ring
    have hw_eA0 : inner ℝ eB0 w = 0 := by
      dsimp [w]
      simpa using inner_cross_right_zero eA0 eB0
    have hw_eB0 : inner ℝ eL w = σ := by rfl
    have hwperp : inner ℝ eA0 w = 0 := by
      dsimp [w]
      simpa using inner_cross_left_zero eA0 eB0
    have heA0_ne : eA0 ≠ 0 := by
      intro hzero
      simpa [hzero] using heA0
    have hσw : w = σ • eL := by
      apply position_eq_of_adapted_coords_eq eA0 eB0 eL w (σ • eL)
      · exact heA0_ne
      · simpa [real_inner_comm] using heAeB0
      · simpa [real_inner_comm] using heL_eA0
      · simpa using heB0
      · simpa using heL_unit
      · simpa [real_inner_comm] using heL_eB0
      · exact hwperp
      · rw [real_inner_smul_right, real_inner_comm, heL_eA0]
        ring
      · calc
          inner ℝ eB0 w = 0 := hw_eA0
          _ = inner ℝ eB0 (σ • eL) := by
                rw [real_inner_smul_right, real_inner_comm, heL_eB0]
                ring
      · calc
          inner ℝ eL w = σ := hw_eB0
          _ = inner ℝ eL (σ • eL) := by
                rw [real_inner_smul_right, heL_unit]
                ring
    have hσsq : σ ^ (2 : Nat) = 1 := by
      have hw_norm : ‖w‖ ^ (2 : Nat) = 1 := by
        calc
          ‖w‖ ^ (2 : Nat)
              = ‖eA0‖ ^ (2 : Nat) * ‖eB0‖ ^ (2 : Nat) - (inner ℝ eA0 eB0) ^ (2 : Nat) := by
                  simpa [w] using norm_cross_sq eA0 eB0
          _ = 1 := by
                rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, heA0, heB0, heAeB0]
                ring
      calc
        σ ^ (2 : Nat) = ‖σ • eL‖ ^ (2 : Nat) := by
          rw [norm_smul, show ‖eL‖ = 1 by
            have : ‖eL‖ ^ (2 : Nat) = 1 := by simpa [real_inner_self_eq_norm_sq] using heL_unit
            nlinarith [norm_nonneg eL], mul_one]
          simp
        _ = ‖w‖ ^ (2 : Nat) := by rw [hσw]
        _ = 1 := hw_norm
    let eA : Vec3 := eA0
    let eB : Vec3 := σ • eB0
    have hLeA : inner ℝ L0 eA = 0 := hLeA0
    have hLeB : inner ℝ L0 eB = 0 := by
      dsimp [eB]
      rw [real_inner_smul_right, hLeB0]
      ring
    have heA : inner ℝ eA eA = 1 := heA0
    have heB : inner ℝ eB eB = 1 := by
      dsimp [eB]
      rw [real_inner_smul_left, real_inner_smul_right, heB0]
      simpa [pow_two] using hσsq
    have heAeB : inner ℝ eA eB = 0 := by
      dsimp [eA, eB]
      rw [real_inner_smul_right, heAeB0]
      ring
    have horient : inner ℝ eL (cross eA eB) = 1 := by
      dsimp [eA, eB, σ]
      rw [cross_smul_right, real_inner_smul_right]
      calc
        inner ℝ eL (cross eA0 eB0) * inner ℝ eL (cross eA0 eB0)
            = σ ^ (2 : Nat) := by ring
        _ = 1 := hσsq
    refine ⟨eA, eB, hLeA, hLeB, heA, heB, heAeB, horient, ?_⟩
    intro t
    let q : Vec3 := (gamma t).1
    let x0 : Real := inner ℝ eA0 q
    let y0 : Real := inner ℝ eB0 q
    let x : Real := inner ℝ eA q
    let y : Real := inner ℝ eB q
    have hy_rel : y = σ * y0 := by
      dsimp [y, y0, eB]
      rw [real_inner_smul_left]
    have hy_sq : y ^ (2 : Nat) = y0 ^ (2 : Nat) := by
      rw [hy_rel]
      nlinarith [hσsq]
    have hcurve0' :
        ((x0 + a * e) ^ (2 : Nat)) / (a ^ (2 : Nat)) +
            (y0 ^ (2 : Nat)) / (b ^ (2 : Nat)) = 1 := by
      simpa [x0, y0, q] using hcurve0 t
    have ha0 : a ≠ 0 := ne_of_gt (semi_major_axis mp gp z0 hE)
    have hb0 : b ≠ 0 := ne_of_gt (semiMinorAxis_pos mp gp z0 hE hL (hgamma.noCollision 0))
    calc
      ((x + a * e) ^ (2 : Nat)) / (a ^ (2 : Nat)) + (y ^ (2 : Nat)) / (b ^ (2 : Nat))
          = ((x0 + a * e) ^ (2 : Nat)) / (a ^ (2 : Nat)) + (y0 ^ (2 : Nat)) / (b ^ (2 : Nat)) := by
              dsimp [x, x0, eA]
              rw [hy_sq]
      _ = 1 := hcurve0'

lemma standardEllipseArealIntegrand
    (a b e θ : Real) :
    (1 / 2 : Real) *
        ((a * (Real.cos θ - e)) * (b * Real.cos θ) -
          (b * Real.sin θ) * (-a * Real.sin θ)) =
      (a * b / 2) * (1 - e * Real.cos θ) := by
  calc
    (1 / 2 : Real) *
        ((a * (Real.cos θ - e)) * (b * Real.cos θ) -
          (b * Real.sin θ) * (-a * Real.sin θ))
        = (a * b / 2) * (Real.cos θ ^ (2 : Nat) + Real.sin θ ^ (2 : Nat) - e * Real.cos θ) := by
            ring
    _ = (a * b / 2) * (1 - e * Real.cos θ) := by
          rw [Real.cos_sq_add_sin_sq]

lemma integral_one_sub_mul_cos_zero_two_pi
    (e : Real) :
    ∫ θ in (0 : Real)..(2 * Real.pi), (1 - e * Real.cos θ) = 2 * Real.pi := by
  have hconst :
      IntervalIntegrable (fun _ : Real => (1 : Real)) MeasureTheory.volume 0 (2 * Real.pi) := by
    exact Continuous.intervalIntegrable continuous_const 0 (2 * Real.pi)
  have hcos :
      IntervalIntegrable (fun θ : Real => e * Real.cos θ) MeasureTheory.volume 0 (2 * Real.pi) := by
    exact Continuous.intervalIntegrable (continuous_const.mul Real.continuous_cos) 0 (2 * Real.pi)
  calc
    ∫ θ in (0 : Real)..(2 * Real.pi), (1 - e * Real.cos θ)
        =
          (∫ θ in (0 : Real)..(2 * Real.pi), (1 : Real)) -
            ∫ θ in (0 : Real)..(2 * Real.pi), e * Real.cos θ := by
              rw [intervalIntegral.integral_sub hconst hcos]
    _ = (2 * Real.pi - 0) - e * (∫ θ in (0 : Real)..(2 * Real.pi), Real.cos θ) := by
          rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
          simp [smul_eq_mul]
    _ = 2 * Real.pi := by
          rw [integral_cos]
          simp

lemma standardEllipseAreaPrimitive_hasDerivAt
    (a b e θ : Real) :
    HasDerivAt
      (fun φ : Real => (a * b / 2) * (φ - e * Real.sin φ))
      ((a * b / 2) * (1 - e * Real.cos θ)) θ := by
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_assoc, mul_left_comm, mul_comm] using
    (((hasDerivAt_id θ).sub ((Real.hasDerivAt_sin θ).const_mul e)).const_mul (a * b / 2))

lemma standardEllipseAreaIntegral_between
    (a b e α β : Real) :
    ∫ θ in α..β, (a * b / 2) * (1 - e * Real.cos θ) =
      (a * b / 2) * (β - e * Real.sin β) -
        (a * b / 2) * (α - e * Real.sin α) := by
  simpa using
    (intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := α) (b := β)
      (f := fun φ : Real => (a * b / 2) * (φ - e * Real.sin φ))
      (f' := fun θ : Real => (a * b / 2) * (1 - e * Real.cos θ))
      (fun θ _hθ => standardEllipseAreaPrimitive_hasDerivAt a b e θ)
      ((by fun_prop :
        Continuous (fun θ : Real => (a * b / 2) * (1 - e * Real.cos θ))).intervalIntegrable α β))

lemma standardEllipseArealIntegral_between
    (a b e α β : Real) :
    ∫ θ in α..β,
        (1 / 2 : Real) *
          ((a * (Real.cos θ - e)) * (b * Real.cos θ) -
            (b * Real.sin θ) * (-a * Real.sin θ)) =
      (a * b / 2) * (β - e * Real.sin β) -
        (a * b / 2) * (α - e * Real.sin α) := by
  rw [show (fun θ : Real =>
      (1 / 2 : Real) *
        ((a * (Real.cos θ - e)) * (b * Real.cos θ) -
          (b * Real.sin θ) * (-a * Real.sin θ))) =
      fun θ : Real => (a * b / 2) * (1 - e * Real.cos θ) by
        funext θ
        exact standardEllipseArealIntegrand a b e θ]
  exact standardEllipseAreaIntegral_between a b e α β

lemma standardEllipseAreaIntegral
    (a b e : Real) :
    ∫ θ in (0 : Real)..(2 * Real.pi),
        (1 / 2 : Real) *
          ((a * (Real.cos θ - e)) * (b * Real.cos θ) -
            (b * Real.sin θ) * (-a * Real.sin θ)) =
      Real.pi * a * b := by
  calc
    ∫ θ in (0 : Real)..(2 * Real.pi),
        (1 / 2 : Real) *
          ((a * (Real.cos θ - e)) * (b * Real.cos θ) -
            (b * Real.sin θ) * (-a * Real.sin θ))
        =
          (a * b / 2) * (2 * Real.pi - e * Real.sin (2 * Real.pi)) -
            (a * b / 2) * (0 - e * Real.sin 0) := by
              simpa using standardEllipseArealIntegral_between a b e 0 (2 * Real.pi)
    _ = Real.pi * a * b := by
          simp
          ring

lemma standardEllipseAreaPrimitive_full_turn
    (a b e α : Real) :
    (a * b / 2) * ((α + 2 * Real.pi) - e * Real.sin (α + 2 * Real.pi)) -
        (a * b / 2) * (α - e * Real.sin α) =
      Real.pi * a * b := by
  rw [Real.sin_add]
  simp
  ring

lemma standardEllipseAreaIntegral_full_turn
    (a b e α : Real) :
    ∫ θ in α..(α + 2 * Real.pi),
        (1 / 2 : Real) *
          ((a * (Real.cos θ - e)) * (b * Real.cos θ) -
            (b * Real.sin θ) * (-a * Real.sin θ)) =
      Real.pi * a * b := by
  calc
    ∫ θ in α..(α + 2 * Real.pi),
        (1 / 2 : Real) *
          ((a * (Real.cos θ - e)) * (b * Real.cos θ) -
            (b * Real.sin θ) * (-a * Real.sin θ))
        =
          (a * b / 2) * ((α + 2 * Real.pi) - e * Real.sin (α + 2 * Real.pi)) -
            (a * b / 2) * (α - e * Real.sin α) := by
              simpa using standardEllipseArealIntegral_between a b e α (α + 2 * Real.pi)
    _ = Real.pi * a * b := by
          exact standardEllipseAreaPrimitive_full_turn a b e α

set_option maxHeartbeats 800000 in
-- Heavy computation in periodicity/traversal proof for ellipse (area integral + injectivity).
-- See configurationPeriod_sweptArea_eq_pi_mul_semiAxes (GS Ch. I §5).
theorem configurationPeriod_traverses_standardEllipse_once
    (mp : MassParam) (gp : GravitationalParam) (gamma : Real -> PhaseSpace)
    (hgamma : IsSolution mp gp gamma) (hE : energy mp gp (gamma 0) < 0)
    (hL : angularMomentum (gamma 0) ≠ 0) {T : Real}
    (hT : HasConfigurationPeriod mp gp gamma T) :
    let z0 := gamma 0
    let L0 := angularMomentum z0
    let e := eccentricity mp gp z0
    let a := semiMajorAxis mp gp z0
    let b := semiMinorAxis mp gp z0
    let eL := (1 / ‖L0‖) • L0
    ∃ eA eB : Vec3, ∃ θ omega : Real → Real,
      inner ℝ L0 eA = 0 ∧
      inner ℝ L0 eB = 0 ∧
      inner ℝ eA eA = 1 ∧
      inner ℝ eB eB = 1 ∧
      inner ℝ eA eB = 0 ∧
      inner ℝ eL (cross eA eB) = 1 ∧
      (∀ t : Real, inner ℝ eA (gamma t).1 = a * (Real.cos (θ t) - e)) ∧
      (∀ t : Real, inner ℝ eB (gamma t).1 = b * Real.sin (θ t)) ∧
      (∀ t : Real, HasDerivAt θ (omega t) t) ∧
      (∀ t : Real,
        signedArealVelocity mp gamma t =
          (a * b / 2) * (1 - e * Real.cos (θ t)) * omega t) ∧
      (∀ t : Real, 0 < omega t) ∧
      θ T = θ 0 + 2 * Real.pi := by
  dsimp
  set z0 : PhaseSpace := gamma 0
  set L0 : Vec3 := angularMomentum z0
  set e : Real := eccentricity mp gp z0
  set a : Real := semiMajorAxis mp gp z0
  set b : Real := semiMinorAxis mp gp z0
  let eL : Vec3 := (1 / ‖L0‖) • L0
  have hL0norm : ‖L0‖ ≠ 0 := norm_ne_zero_iff.mpr (by simpa [z0, L0] using hL)
  have hL0pos : 0 < ‖L0‖ := norm_pos_iff.mpr (by simpa [z0, L0] using hL)
  have ha : 0 < a := by simpa [z0, a] using semi_major_axis mp gp z0 hE
  have hb : 0 < b := by
    simpa [z0, b] using semiMinorAxis_pos mp gp z0 hE
      (by simpa [z0, L0] using hL) (hgamma.noCollision 0)
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hm0 : mp.m ≠ 0 := ne_of_gt mp.hm
  have he0 : 0 ≤ e := by simpa [z0, e] using eccentricity_nonneg mp gp z0
  have he1 : e < 1 := by
    simpa [z0, e] using eccentricity_lt_one mp gp z0 hE
      (by simpa [z0, L0] using hL) (hgamma.noCollision 0)
  have horientedEllipse :=
    kepler_first_law_oriented_standardEllipse mp gp gamma hgamma hE hL
  have horientedEllipse' :
      ∃ eA eB : Vec3,
        inner ℝ L0 eA = 0 ∧
        inner ℝ L0 eB = 0 ∧
        inner ℝ eA eA = 1 ∧
        inner ℝ eB eB = 1 ∧
        inner ℝ eA eB = 0 ∧
        inner ℝ eL (cross eA eB) = 1 ∧
        ∀ t : Real,
          let q := (gamma t).1
          let x := inner ℝ eA q
          let y := inner ℝ eB q
          ((x + a * e) ^ (2 : Nat)) / (a ^ (2 : Nat)) +
              (y ^ (2 : Nat)) / (b ^ (2 : Nat)) =
            1 := by
    simpa [z0, L0, e, a, b, eL] using horientedEllipse
  rcases horientedEllipse' with
    ⟨eA, eB, hLeA, hLeB, heA, heB, heAeB, horient, hcurve⟩
  let x : Real → Real := fun t => inner ℝ eA (gamma t).1
  let y : Real → Real := fun t => inner ℝ eB (gamma t).1
  let px : Real → Real := fun t => inner ℝ eA (gamma t).2
  let py : Real → Real := fun t => inner ℝ eB (gamma t).2
  let u : Real → Real := fun t => (x t + a * e) / a
  let v : Real → Real := fun t => y t / b
  let ux : Real → Real := fun t => px t / (mp.m * a)
  let vy : Real → Real := fun t => py t / (mp.m * b)
  have hcircle : ∀ t : Real, u t ^ (2 : Nat) + v t ^ (2 : Nat) = 1 := by
    intro t
    have hc := hcurve t
    dsimp [u, v, x, y] at hc ⊢
    field_simp [ha0, hb0] at hc ⊢
    nlinarith
  have hq : ∀ t : Real, HasDerivAt (fun τ : Real => (gamma τ).1) ((1 / mp.m) • (gamma t).2) t := by
    intro t
    let fstCLM : PhaseSpace →L[ℝ] Vec3 := ContinuousLinearMap.fst ℝ Vec3 Vec3
    have hfst :
        HasDerivAt (fun τ : Real => fstCLM (gamma τ))
          (fstCLM (keplerVectorField mp gp (gamma t))) t := by
      exact fstCLM.hasFDerivAt.comp_hasDerivAt t (hgamma.ode t)
    simpa [fstCLM, hgamma.position_rhs t] using hfst
  have hx : ∀ t : Real, HasDerivAt x (px t / mp.m) t := by
    intro t
    have h0 :
        HasDerivAt (fun s : Real => eA 0 * (gamma s).1 0)
          (eA 0 * ((gamma t).2 0 / mp.m)) t :=
      (hgamma.hasDerivAt_position_coord t 0).const_mul (eA 0)
    have h1 :
        HasDerivAt (fun s : Real => eA 1 * (gamma s).1 1)
          (eA 1 * ((gamma t).2 1 / mp.m)) t :=
      (hgamma.hasDerivAt_position_coord t 1).const_mul (eA 1)
    have h2 :
        HasDerivAt (fun s : Real => eA 2 * (gamma s).1 2)
          (eA 2 * ((gamma t).2 2 / mp.m)) t :=
      (hgamma.hasDerivAt_position_coord t 2).const_mul (eA 2)
    have hsum :
        HasDerivAt
          (fun s : Real =>
            eA 0 * (gamma s).1 0 + eA 1 * (gamma s).1 1 + eA 2 * (gamma s).1 2)
          (eA 0 * ((gamma t).2 0 / mp.m) +
            eA 1 * ((gamma t).2 1 / mp.m) + eA 2 * ((gamma t).2 2 / mp.m)) t := by
      simpa [add_assoc] using (h0.add h1).add h2
    convert hsum using 1
    · funext s
      simpa [x, inner_fin3, add_assoc]
    · simp [px, inner_fin3, div_eq_mul_inv]
      ring
  have hy : ∀ t : Real, HasDerivAt y (py t / mp.m) t := by
    intro t
    have h0 :
        HasDerivAt (fun s : Real => eB 0 * (gamma s).1 0)
          (eB 0 * ((gamma t).2 0 / mp.m)) t :=
      (hgamma.hasDerivAt_position_coord t 0).const_mul (eB 0)
    have h1 :
        HasDerivAt (fun s : Real => eB 1 * (gamma s).1 1)
          (eB 1 * ((gamma t).2 1 / mp.m)) t :=
      (hgamma.hasDerivAt_position_coord t 1).const_mul (eB 1)
    have h2 :
        HasDerivAt (fun s : Real => eB 2 * (gamma s).1 2)
          (eB 2 * ((gamma t).2 2 / mp.m)) t :=
      (hgamma.hasDerivAt_position_coord t 2).const_mul (eB 2)
    have hsum :
        HasDerivAt
          (fun s : Real =>
            eB 0 * (gamma s).1 0 + eB 1 * (gamma s).1 1 + eB 2 * (gamma s).1 2)
          (eB 0 * ((gamma t).2 0 / mp.m) +
            eB 1 * ((gamma t).2 1 / mp.m) + eB 2 * ((gamma t).2 2 / mp.m)) t := by
      simpa [add_assoc] using (h0.add h1).add h2
    convert hsum using 1
    · funext s
      simpa [y, inner_fin3, add_assoc]
    · simp [py, inner_fin3, div_eq_mul_inv]
      ring
  have hu : ∀ t : Real, HasDerivAt u (ux t) t := by
    intro t
    simpa [u, ux, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm]
      using ((hx t).add_const (a * e)).const_mul (1 / a)
  have hv : ∀ t : Real, HasDerivAt v (vy t) t := by
    intro t
    simpa [v, vy, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      using (hy t).const_mul (1 / b)
  have hqdecomp : ∀ t : Real, (gamma t).1 = x t • eA + y t • eB := by
    intro t
    apply position_eq_of_adapted_coords_eq L0 eA eB (gamma t).1 (x t • eA + y t • eB)
    · simpa [z0, L0] using hL
    · exact hLeA
    · exact hLeB
    · exact heA
    · exact heB
    · exact heAeB
    · simpa [z0, L0] using (planarity mp gp gamma hgamma hL t).1
    · have hxeA : inner ℝ L0 (x t • eA) = 0 := by
        rw [real_inner_smul_right, hLeA]
        ring_nf
      have hyeB : inner ℝ L0 (y t • eB) = 0 := by
        rw [real_inner_smul_right, hLeB]
        ring_nf
      calc
        inner ℝ L0 (x t • eA + y t • eB)
            = inner ℝ L0 (x t • eA) + inner ℝ L0 (y t • eB) := by
                rw [inner_add_right]
        _ = 0 + 0 := by rw [hxeA, hyeB]
        _ = 0 := by ring
    · have heA_normsq : ‖eA‖ ^ (2 : Nat) = 1 := by
        simpa [real_inner_self_eq_norm_sq] using heA
      have hxeA : inner ℝ eA (x t • eA) = x t := by
        rw [real_inner_smul_right, real_inner_self_eq_norm_sq, heA_normsq]
        ring_nf
      have hyeB : inner ℝ eA (y t • eB) = 0 := by
        rw [real_inner_smul_right, heAeB]
        ring_nf
      calc
        inner ℝ eA (gamma t).1 = x t := by simp [x]
        _ = x t + 0 := by ring
        _ = inner ℝ eA (x t • eA) + inner ℝ eA (y t • eB) := by rw [hxeA, hyeB]
        _ = inner ℝ eA (x t • eA + y t • eB) := by rw [inner_add_right]
    · have heB_normsq : ‖eB‖ ^ (2 : Nat) = 1 := by
        simpa [real_inner_self_eq_norm_sq] using heB
      have hxeA : inner ℝ eB (x t • eA) = 0 := by
        rw [real_inner_smul_right, real_inner_comm, heAeB]
        ring_nf
      have hyeB : inner ℝ eB (y t • eB) = y t := by
        rw [real_inner_smul_right, real_inner_self_eq_norm_sq, heB_normsq]
        ring_nf
      calc
        inner ℝ eB (gamma t).1 = y t := by simp [y]
        _ = 0 + y t := by ring
        _ = inner ℝ eB (x t • eA) + inner ℝ eB (y t • eB) := by rw [hxeA, hyeB]
        _ = inner ℝ eB (x t • eA + y t • eB) := by rw [inner_add_right]
  have hpdecomp : ∀ t : Real, (gamma t).2 = px t • eA + py t • eB := by
    intro t
    apply position_eq_of_adapted_coords_eq L0 eA eB (gamma t).2 (px t • eA + py t • eB)
    · simpa [z0, L0] using hL
    · exact hLeA
    · exact hLeB
    · exact heA
    · exact heB
    · exact heAeB
    · simpa [z0, L0] using (planarity mp gp gamma hgamma hL t).2
    · have hxeA : inner ℝ L0 (px t • eA) = 0 := by
        rw [real_inner_smul_right, hLeA]
        ring_nf
      have hyeB : inner ℝ L0 (py t • eB) = 0 := by
        rw [real_inner_smul_right, hLeB]
        ring_nf
      calc
        inner ℝ L0 (px t • eA + py t • eB)
            = inner ℝ L0 (px t • eA) + inner ℝ L0 (py t • eB) := by
                rw [inner_add_right]
        _ = 0 + 0 := by rw [hxeA, hyeB]
        _ = 0 := by ring
    · have heA_normsq : ‖eA‖ ^ (2 : Nat) = 1 := by
        simpa [real_inner_self_eq_norm_sq] using heA
      have hxeA : inner ℝ eA (px t • eA) = px t := by
        rw [real_inner_smul_right, real_inner_self_eq_norm_sq, heA_normsq]
        ring_nf
      have hyeB : inner ℝ eA (py t • eB) = 0 := by
        rw [real_inner_smul_right, heAeB]
        ring_nf
      calc
        inner ℝ eA (gamma t).2 = px t := by simp [px]
        _ = px t + 0 := by ring
        _ = inner ℝ eA (px t • eA) + inner ℝ eA (py t • eB) := by rw [hxeA, hyeB]
        _ = inner ℝ eA (px t • eA + py t • eB) := by rw [inner_add_right]
    · have heB_normsq : ‖eB‖ ^ (2 : Nat) = 1 := by
        simpa [real_inner_self_eq_norm_sq] using heB
      have hxeA : inner ℝ eB (px t • eA) = 0 := by
        rw [real_inner_smul_right, real_inner_comm, heAeB]
        ring_nf
      have hyeB : inner ℝ eB (py t • eB) = py t := by
        rw [real_inner_smul_right, real_inner_self_eq_norm_sq, heB_normsq]
        ring_nf
      calc
        inner ℝ eB (gamma t).2 = py t := by simp [py]
        _ = 0 + py t := by ring
        _ = inner ℝ eB (px t • eA) + inner ℝ eB (py t • eB) := by rw [hxeA, hyeB]
        _ = inner ℝ eB (px t • eA + py t • eB) := by rw [inner_add_right]
  have hcross : ∀ t : Real,
      cross (gamma t).1 (gamma t).2 =
        (x t * py t - y t * px t) • cross eA eB := by
    intro t
    calc
      cross (gamma t).1 (gamma t).2
          = cross (x t • eA + y t • eB) (px t • eA + py t • eB) := by
              rw [hqdecomp t, hpdecomp t]
      _ = cross (x t • eA) (px t • eA) + cross (x t • eA) (py t • eB) +
            (cross (y t • eB) (px t • eA) + cross (y t • eB) (py t • eB)) := by
              rw [cross_add_left, cross_add_right, cross_add_right]
      _ = 0 + (py t * x t) • cross eA eB + ((px t * y t) • cross eB eA + 0) := by
              simp [cross_smul_left, cross_smul_right, cross_self, smul_smul]
      _ = 0 + (x t * py t) • cross eA eB + ((y t * px t) • cross eB eA + 0) := by
              ring_nf
      _ = (x t * py t - y t * px t) • cross eA eB := by
              have hanti : cross eB eA = -cross eA eB := by
                ext i
                fin_cases i <;> simp [cross, cross_apply] <;> ring
              calc
                0 + (x t * py t) • cross eA eB + ((y t * px t) • cross eB eA + 0)
                    = (x t * py t) • cross eA eB - (y t * px t) • cross eA eB := by
                        rw [hanti]
                        simp [sub_eq_add_neg]
                _ = (x t * py t - y t * px t) • cross eA eB := by
                        rw [sub_smul]
  have hAVxy : ∀ t : Real,
      2 * mp.m * signedArealVelocity mp gamma t = x t * py t - y t * px t := by
    intro t
    unfold signedArealVelocity
    calc
      2 * mp.m *
          ((1 / (2 * mp.m)) * inner ℝ ((1 / ‖angularMomentum (gamma 0)‖) • angularMomentum (gamma 0))
            (cross (gamma t).1 (gamma t).2))
          = inner ℝ eL (cross (gamma t).1 (gamma t).2) := by
              dsimp [eL, z0, L0]
              field_simp [hm0]
      _ = inner ℝ eL ((x t * py t - y t * px t) • cross eA eB) := by rw [hcross t]
      _ = x t * py t - y t * px t := by rw [real_inner_smul_right, horient, mul_one]
  have hphi : ∀ t : Real,
      (u t - e) * vy t - v t * ux t = ‖L0‖ / (a * b * mp.m) := by
    intro t
    have habm0 : a * b * mp.m ≠ 0 := by positivity
    have hnorm_eq : x t * py t - y t * px t = ‖L0‖ := by
      have hm2 : 2 * mp.m ≠ 0 := by nlinarith [mp.hm]
      calc
        x t * py t - y t * px t = 2 * mp.m * signedArealVelocity mp gamma t := by
          symm
          exact hAVxy t
        _ = 2 * mp.m * (‖L0‖ / (2 * mp.m)) := by simpa [z0, L0] using congrArg (fun z => 2 * mp.m * z) (kepler_second_law mp gp gamma hgamma hL t)
        _ = ‖L0‖ := by field_simp [hm2]
    have hxy_expr :
        (u t - e) * vy t - v t * ux t =
          (x t * py t - y t * px t) / (a * b * mp.m) := by
      dsimp [x, y, px, py, u, v, ux, vy]
      field_simp [ha0, hb0, hm0]
      ring
    calc
      (u t - e) * vy t - v t * ux t = (x t * py t - y t * px t) / (a * b * mp.m) := hxy_expr
      _ = ‖L0‖ / (a * b * mp.m) := by rw [hnorm_eq]
  have hcircleDeriv : ∀ t : Real, u t * ux t + v t * vy t = 0 := by
    intro t
    have hsum : HasDerivAt (fun s : Real => u s ^ (2 : Nat) + v s ^ (2 : Nat))
        (2 * u t * ux t + 2 * v t * vy t) t := by
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm]
        using ((hu t).pow 2).add ((hv t).pow 2)
    have hsumDeriv :
        deriv (fun s : Real => u s ^ (2 : Nat) + v s ^ (2 : Nat)) t =
          2 * u t * ux t + 2 * v t * vy t := by
      simpa using hsum.deriv
    have hconstDeriv :
        deriv (fun s : Real => u s ^ (2 : Nat) + v s ^ (2 : Nat)) t = 0 := by
      have hfun : (fun s : Real => u s ^ (2 : Nat) + v s ^ (2 : Nat)) = fun _ : Real => 1 := by
        funext s
        exact hcircle s
      simpa [hfun] using (hasDerivAt_const t (1 : Real)).deriv
    nlinarith [hsumDeriv, hconstDeriv]
  have hdenpos : ∀ t : Real, 0 < 1 - e * u t := by
    intro t
    have hu_le : u t ≤ 1 := by
      have hc := hcircle t
      nlinarith [sq_nonneg (v t), hc]
    nlinarith
  let omega : Real → Real := fun t => ‖L0‖ / (a * b * mp.m * (1 - e * u t))
  have homegaPos : ∀ t : Real, 0 < omega t := by
    intro t
    dsimp [omega]
    have hbase : 0 < a * b * mp.m := by
      exact mul_pos (mul_pos ha hb) mp.hm
    have hden : 0 < a * b * mp.m * (1 - e * u t) := by
      exact mul_pos hbase (hdenpos t)
    exact div_pos hL0pos hden
  have huODE : ∀ t : Real, ux t = -omega t * v t := by
    intro t
    have huv : u t * ux t = -(v t * vy t) := by
      nlinarith [hcircleDeriv t]
    have hvv : v t * vy t = -(u t * ux t) := by
      nlinarith [hcircleDeriv t]
    have hmul :
        (1 - e * u t) * ux t = -v t * (‖L0‖ / (a * b * mp.m)) := by
      calc
        (1 - e * u t) * ux t = (u t ^ (2 : Nat) + v t ^ (2 : Nat) - e * u t) * ux t := by
          rw [hcircle t]
        _ = u t * (u t * ux t) + v t * (v t * ux t) - e * u t * ux t := by ring
        _ = u t * (-(v t * vy t)) + v t * (v t * ux t) + e * (v t * vy t) := by
              rw [huv, hvv]
              ring
        _ = -v t * ((u t - e) * vy t - v t * ux t) := by ring
        _ = -v t * (‖L0‖ / (a * b * mp.m)) := by rw [hphi t]
    have hscale :
        ‖L0‖ / (a * b * mp.m) = (1 - e * u t) * omega t := by
      dsimp [omega]
      field_simp [ha0, hb0, hm0, (ne_of_gt (hdenpos t))]
    have hmul' :
        (1 - e * u t) * ux t = (1 - e * u t) * (-omega t * v t) := by
      calc
        (1 - e * u t) * ux t = -v t * (‖L0‖ / (a * b * mp.m)) := hmul
        _ = -v t * ((1 - e * u t) * omega t) := by rw [hscale]
        _ = (1 - e * u t) * (-omega t * v t) := by ring
    exact (mul_left_cancel₀ (ne_of_gt (hdenpos t))) hmul'
  have hvODE : ∀ t : Real, vy t = omega t * u t := by
    intro t
    have hvv : v t * vy t = -(u t * ux t) := by
      nlinarith [hcircleDeriv t]
    have hmul :
        (1 - e * u t) * vy t = u t * (‖L0‖ / (a * b * mp.m)) := by
      calc
        (1 - e * u t) * vy t = (u t ^ (2 : Nat) + v t ^ (2 : Nat) - e * u t) * vy t := by
          rw [hcircle t]
        _ = u t * ((u t - e) * vy t) + v t * (v t * vy t) := by ring
        _ = u t * ((u t - e) * vy t) - v t * (u t * ux t) := by
              rw [hvv]
              ring
        _ = u t * ((u t - e) * vy t - v t * ux t) := by ring
        _ = u t * (‖L0‖ / (a * b * mp.m)) := by rw [hphi t]
    have hscale :
        ‖L0‖ / (a * b * mp.m) = (1 - e * u t) * omega t := by
      dsimp [omega]
      field_simp [ha0, hb0, hm0, (ne_of_gt (hdenpos t))]
    have hmul' :
        (1 - e * u t) * vy t = (1 - e * u t) * (omega t * u t) := by
      calc
        (1 - e * u t) * vy t = u t * (‖L0‖ / (a * b * mp.m)) := hmul
        _ = u t * ((1 - e * u t) * omega t) := by rw [hscale]
        _ = (1 - e * u t) * (omega t * u t) := by ring
    exact (mul_left_cancel₀ (ne_of_gt (hdenpos t))) hmul'
  have hu' : ∀ t : Real, HasDerivAt u (-omega t * v t) t := by
    intro t
    simpa [huODE t] using hu t
  have hv' : ∀ t : Real, HasDerivAt v (omega t * u t) t := by
    intro t
    simpa [hvODE t] using hv t
  have homegaCont : Continuous omega := by
    have huCont : Continuous u := continuous_iff_continuousAt.2 fun t => (hu t).continuousAt
    have hdenCont : Continuous fun t : Real => a * b * mp.m * (1 - e * u t) := by
      exact continuous_const.mul (continuous_const.sub (continuous_const.mul huCont))
    exact continuous_const.div hdenCont (fun t => ne_of_gt (by
      exact mul_pos (mul_pos ha hb) mp.hm |> fun hbase => mul_pos hbase (hdenpos t)))
  rcases curve_on_standardEllipse_exists_angle gamma eA eB a b e ha hb hcurve 0 with
    ⟨θ0, hθ0x, hθ0y⟩
  let θ : Real → Real := fun t => θ0 + ∫ τ in 0..t, omega τ
  have hθ : ∀ t : Real, HasDerivAt θ (omega t) t := by
    intro t
    simpa [θ] using (homegaCont.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add θ0
  have h0θ : θ 0 = θ0 := by simp [θ]
  have h0u : u 0 = Real.cos (θ 0) := by
    rw [h0θ]
    have hx0 : x 0 = a * (Real.cos θ0 - e) := by simpa [x] using hθ0x
    dsimp [u]
    rw [hx0]
    field_simp [ha0]
    ring
  have h0v : v 0 = Real.sin (θ 0) := by
    rw [h0θ]
    have hy0 : y 0 = b * Real.sin θ0 := by simpa [y] using hθ0y
    dsimp [v]
    rw [hy0]
    field_simp [hb0]
  have htrig := unitCircle_eq_cos_sin_of_hasDerivAt hu' hv' hθ h0u h0v
  have hθderiv : ∀ t : Real, deriv θ t = omega t := by
    intro t
    simpa using (hθ t).deriv
  have hθmono : StrictMono θ := strictMono_of_deriv_pos fun t => by
    rw [hθderiv]
    exact homegaPos t
  have hθCont : Continuous θ := continuous_iff_continuousAt.2 fun t => (hθ t).continuousAt
  have huper : u T = u 0 := by
    dsimp [u, x]
    simpa using congrArg (fun q : Vec3 => (inner ℝ eA q + a * e) / a) (hT.periodic 0)
  have hvørper : v T = v 0 := by
    dsimp [v, y]
    simpa using congrArg (fun q : Vec3 => inner ℝ eB q / b) (hT.periodic 0)
  have hcosEq : Real.cos (θ T) = Real.cos (θ 0) := by
    rw [← (htrig T).1, ← (htrig 0).1, huper]
  have hsinEq : Real.sin (θ T) = Real.sin (θ 0) := by
    rw [← (htrig T).2, ← (htrig 0).2, hvørper]
  have hangle : ((θ T : Real.Angle)) = (θ 0) := Real.Angle.cos_sin_inj hcosEq hsinEq
  rcases Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp hangle with ⟨k, hk⟩
  have hkRealPos : 0 < (k : Real) := by
    have hlt : θ 0 < θ T := hθmono hT.pos
    nlinarith [hk, Real.pi_pos]
  have hkPos : 0 < k := by
    by_contra hkNotPos
    have hkLe : (k : Real) ≤ 0 := by
      exact_mod_cast (le_of_not_gt hkNotPos)
    linarith
  have hkOne : k = 1 := by
    by_contra hkNeOne
    have hkGeTwo : 2 ≤ k := by omega
    have htarget :
        θ 0 + 2 * Real.pi ∈ Set.Ioo (θ 0) (θ T) := by
      constructor
      · nlinarith [Real.pi_pos]
      · have hkGeTwo' : (2 : Real) ≤ k := by exact_mod_cast hkGeTwo
        nlinarith [hk, Real.pi_pos]
    rcases intermediate_value_Ioo hT.pos.le hθCont.continuousOn htarget with ⟨t, ht, htθ⟩
    have hEq :=
      configurationPeriod_eq_or_endpoints_of_same_standardEllipse_angle
        mp gp gamma hgamma hL hT hLeA hLeB heA heB heAeB
        ⟨le_rfl, hT.pos.le⟩ ⟨ht.1.le, ht.2.le⟩
        (by simpa [h0θ] using hθ0x)
        (by simpa [h0θ] using hθ0y)
        (by
          calc
            inner ℝ eA (gamma t).1 = x t := by simp [x]
            _ = a * (u t - e) := by
              dsimp [u]
              field_simp [ha0]
              ring
            _ = a * (Real.cos (θ t) - e) := by rw [(htrig t).1])
        (by
          calc
            inner ℝ eB (gamma t).1 = y t := by simp [y]
            _ = b * v t := by
              dsimp [v]
              field_simp [hb0]
            _ = b * Real.sin (θ t) := by rw [(htrig t).2])
        (by
          rw [htθ]
          simpa [h0θ] using (Real.cos_add_two_pi θ0).symm)
        (by
          rw [htθ]
          simpa [h0θ] using (Real.sin_add_two_pi θ0).symm)
    rcases hEq with hEq | hEq | hEq
    · have : ¬ t = 0 := by linarith [ht.1]
      exact (this hEq.symm).elim
    · rcases hEq with ⟨_, hEqT⟩
      have : ¬ t = T := by linarith [ht.2, hT.pos]
      exact (this hEqT).elim
    · rcases hEq with ⟨h0T, hEq0⟩
      have : ¬ t = 0 := by linarith [ht.1]
      exact (this hEq0).elim
  have hturn : θ T = θ 0 + 2 * Real.pi := by
    have hkOne' : (k : Real) = 1 := by exact_mod_cast hkOne
    have hdiff : θ T - θ 0 = 2 * Real.pi := by simpa [hkOne'] using hk
    linarith
  have hAreal :
      ∀ t : Real,
        signedArealVelocity mp gamma t =
          (a * b / 2) * (1 - e * Real.cos (θ t)) * omega t := by
    intro t
    rw [kepler_second_law mp gp gamma hgamma hL t, ← (htrig t).1]
    dsimp [omega]
    field_simp [ha0, hb0, hm0, (ne_of_gt (hdenpos t))]
    ring
  refine ⟨eA, eB, θ, omega, hLeA, hLeB, heA, heB, heAeB, horient, ?_, ?_, hθ, hAreal, homegaPos, hturn⟩
  · intro t
    have hxt := (htrig t).1
    have hu_def : a * u t = x t + a * e := by
      dsimp [u]
      field_simp [ha0]
    have hx_eq : x t + a * e = a * Real.cos (θ t) := by
      calc
        x t + a * e = a * u t := by simpa [hu_def] using hu_def.symm
        _ = a * Real.cos (θ t) := by rw [hxt]
    calc
      inner ℝ eA (gamma t).1 = x t := by simp [x]
      _ = a * (Real.cos (θ t) - e) := by nlinarith [hx_eq]
  · intro t
    have hyt := (htrig t).2
    have hv_def : b * v t = y t := by
      dsimp [v]
      field_simp [hb0]
    have hy_eq : y t = b * Real.sin (θ t) := by
      calc
        y t = b * v t := by simpa [hv_def] using hv_def.symm
        _ = b * Real.sin (θ t) := by rw [hyt]
    calc
      inner ℝ eB (gamma t).1 = y t := by simp [y]
      _ = b * Real.sin (θ t) := hy_eq

set_option maxHeartbeats 800000 in
-- Heavy integral + trig simplification for swept area = π a b (core of 3rd law).
-- Matches GS Ch. I §5 area argument.
theorem configurationPeriod_sweptArea_eq_pi_mul_semiAxes
    (mp : MassParam) (gp : GravitationalParam) (gamma : Real -> PhaseSpace)
    (hgamma : IsSolution mp gp gamma) (hE : energy mp gp (gamma 0) < 0)
    (hL : angularMomentum (gamma 0) ≠ 0) {T : Real}
    (hT : HasConfigurationPeriod mp gp gamma T) :
    sweptAreaOn mp gamma 0 T =
      Real.pi * semiMajorAxis mp gp (gamma 0) * semiMinorAxis mp gp (gamma 0) := by
  set z0 : PhaseSpace := gamma 0
  set L0 : Vec3 := angularMomentum z0
  set e : Real := eccentricity mp gp z0
  set a : Real := semiMajorAxis mp gp z0
  set b : Real := semiMinorAxis mp gp z0
  let eL : Vec3 := (1 / ‖L0‖) • L0
  have hL0norm : ‖L0‖ ≠ 0 := norm_ne_zero_iff.mpr (by simpa [z0, L0] using hL)
  have hL0pos : 0 < ‖L0‖ := norm_pos_iff.mpr (by simpa [z0, L0] using hL)
  have ha : 0 < a := by simpa [z0, a] using semi_major_axis mp gp z0 hE
  have hb : 0 < b := by
    simpa [z0, b] using semiMinorAxis_pos mp gp z0 hE (by simpa [z0, L0] using hL) (hgamma.noCollision 0)
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hb0 : b ≠ 0 := ne_of_gt hb
  have htrav := configurationPeriod_traverses_standardEllipse_once mp gp gamma hgamma hE hL hT
  dsimp [z0, L0, e, a, b, eL] at htrav
  obtain ⟨eA, eB, θ, omega, _hLeA, _hLeB, _heA, _heB, _heAeB, _horient, _hxθ, _hyθ,
    hθ, hAreal, _homegaPos, hturn⟩ :
      ∃ eA eB : Vec3, ∃ θ omega : Real → Real,
        inner ℝ L0 eA = 0 ∧
          inner ℝ L0 eB = 0 ∧
            inner ℝ eA eA = 1 ∧
              inner ℝ eB eB = 1 ∧
                inner ℝ eA eB = 0 ∧
                  inner ℝ eL (cross eA eB) = 1 ∧
                    (∀ t : Real, inner ℝ eA (gamma t).1 = a * (Real.cos (θ t) - e)) ∧
                      (∀ t : Real, inner ℝ eB (gamma t).1 = b * Real.sin (θ t)) ∧
                        (∀ t : Real, HasDerivAt θ (omega t) t) ∧
                          (∀ t : Real,
                            signedArealVelocity mp gamma t =
                              (a * b / 2) * (1 - e * Real.cos (θ t)) * omega t) ∧
                            (∀ t : Real, 0 < omega t) ∧
                              θ T = θ 0 + 2 * Real.pi := htrav
  have hderArea :
      ∀ t ∈ Set.uIcc 0 T,
        HasDerivAt
          (fun s : Real => (a * b / 2) * (θ s - e * Real.sin (θ s)))
          (signedArealVelocity mp gamma t) t := by
    intro t _ht
    have hF :
        HasDerivAt
          (fun s : Real => (a * b / 2) * (θ s - e * Real.sin (θ s)))
          ((a * b / 2) * (1 - e * Real.cos (θ t)) * omega t) t := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm]
        using (standardEllipseAreaPrimitive_hasDerivAt a b e (θ t)).comp t (hθ t)
    simpa [hAreal t] using hF
  have hint :
      IntervalIntegrable (fun t : Real => signedArealVelocity mp gamma t) MeasureTheory.volume 0 T := by
    rw [show (fun t : Real => signedArealVelocity mp gamma t) =
        fun _ : Real => ‖L0‖ / (2 * mp.m) by
          funext t
          simpa [z0, L0] using kepler_second_law mp gp gamma hgamma hL t]
    exact Continuous.intervalIntegrable continuous_const 0 T
  calc
    sweptAreaOn mp gamma 0 T
        = (a * b / 2) * (θ T - e * Real.sin (θ T)) -
            (a * b / 2) * (θ 0 - e * Real.sin (θ 0)) := by
              unfold sweptAreaOn
              simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt hderArea hint
    _ = Real.pi * a * b := by
          simpa [hturn] using standardEllipseAreaPrimitive_full_turn a b e (θ 0)
    _ = Real.pi * semiMajorAxis mp gp (gamma 0) * semiMinorAxis mp gp (gamma 0) := by
          simp [z0, a, b]

theorem period_times_normL_eq_two_m_pi_ab
    (mp : MassParam) (gp : GravitationalParam) (gamma : Real -> PhaseSpace)
    (hgamma : IsSolution mp gp gamma) (hL : angularMomentum (gamma 0) ≠ 0) {T : Real}
    (_hT : HasConfigurationPeriod mp gp gamma T)
    (harea :
      sweptAreaOn mp gamma 0 T =
        Real.pi * semiMajorAxis mp gp (gamma 0) * semiMinorAxis mp gp (gamma 0)) :
    T * ‖angularMomentum (gamma 0)‖ =
      2 * mp.m * Real.pi * semiMajorAxis mp gp (gamma 0) * semiMinorAxis mp gp (gamma 0) := by
  set z0 : PhaseSpace := gamma 0
  set a : Real := semiMajorAxis mp gp z0
  set b : Real := semiMinorAxis mp gp z0
  set L0 : Vec3 := angularMomentum z0
  have hswept := sweptAreaOn_eq_interval_mul_areal_velocity mp gp gamma hgamma hL 0 T
  have harea' :
      T * (‖L0‖ / (2 * mp.m)) = Real.pi * a * b := by
    calc
      T * (‖L0‖ / (2 * mp.m)) = sweptAreaOn mp gamma 0 T := by
        simpa [z0, L0] using hswept.symm
      _ = Real.pi * a * b := by simpa [z0, a, b] using harea
  have hm2 : 2 * mp.m ≠ 0 := by nlinarith [mp.hm]
  have hcancel : (2 * mp.m) * (‖L0‖ / (2 * mp.m)) = ‖L0‖ := by
    rw [div_eq_mul_inv]
    calc
      (2 * mp.m) * (‖L0‖ * (2 * mp.m)⁻¹)
          = ‖L0‖ * ((2 * mp.m) * (2 * mp.m)⁻¹) := by ring
      _ = ‖L0‖ * 1 := by rw [mul_inv_cancel₀ hm2]
      _ = ‖L0‖ := by ring
  calc
    T * ‖L0‖ = T * ((2 * mp.m) * (‖L0‖ / (2 * mp.m))) := by rw [hcancel]
    _ = (2 * mp.m) * (T * (‖L0‖ / (2 * mp.m))) := by ring
    _ = (2 * mp.m) * (Real.pi * a * b) := by rw [harea']
    _ = 2 * mp.m * Real.pi * a * b := by ring

theorem kepler_third_law_of_period_and_area
    (mp : MassParam) (gp : GravitationalParam) (gamma : Real -> PhaseSpace)
    (hgamma : IsSolution mp gp gamma) (hH : energy mp gp (gamma 0) < 0)
    (hL : angularMomentum (gamma 0) ≠ 0) {T : Real}
    (hT : HasConfigurationPeriod mp gp gamma T)
    (harea :
      sweptAreaOn mp gamma 0 T =
        Real.pi * semiMajorAxis mp gp (gamma 0) * semiMinorAxis mp gp (gamma 0)) :
    T ^ (2 : Nat) =
      (4 * Real.pi ^ (2 : Nat) * mp.m / gp.mu) *
        (semiMajorAxis mp gp (gamma 0)) ^ (3 : Nat) := by
  set z0 : PhaseSpace := gamma 0
  set a : Real := semiMajorAxis mp gp z0
  set b : Real := semiMinorAxis mp gp z0
  set L0 : Vec3 := angularMomentum z0
  have hmul :=
    period_times_normL_eq_two_m_pi_ab mp gp gamma hgamma hL hT harea
  have hnormL0 : ‖L0‖ ≠ 0 := norm_ne_zero_iff.mpr (by simpa [z0, L0] using hL)
  have hmul_sq :
      T ^ (2 : Nat) * ‖L0‖ ^ (2 : Nat) =
        4 * Real.pi ^ (2 : Nat) * mp.m ^ (2 : Nat) * a ^ (2 : Nat) * b ^ (2 : Nat) := by
    have hsq := congrArg (fun x : Real => x ^ (2 : Nat)) hmul
    nlinarith [hsq]
  have hb_sq :
      b ^ (2 : Nat) = a * (‖L0‖ ^ (2 : Nat) / (mp.m * gp.mu)) := by
    calc
      b ^ (2 : Nat) = a * semiLatusRectum mp gp z0 := by
        simpa [z0, a, b] using semiMinorAxis_sq mp gp z0 hH (by simpa [z0, L0] using hL)
          (hgamma.noCollision 0)
      _ = a * (‖L0‖ ^ (2 : Nat) / (mp.m * gp.mu)) := by
        simp [semiLatusRectum, z0, L0]
  have htarget_mul :
      ((4 * Real.pi ^ (2 : Nat) * mp.m / gp.mu) * a ^ (3 : Nat)) *
          ‖L0‖ ^ (2 : Nat) =
        4 * Real.pi ^ (2 : Nat) * mp.m ^ (2 : Nat) * a ^ (2 : Nat) * b ^ (2 : Nat) := by
    rw [hb_sq]
    field_simp [hnormL0, ne_of_gt mp.hm, ne_of_gt gp.hmu]
  have hnorm_sq_ne : ‖L0‖ ^ (2 : Nat) ≠ 0 := pow_ne_zero 2 hnormL0
  apply (mul_right_cancel₀ hnorm_sq_ne)
  calc
    T ^ (2 : Nat) * ‖L0‖ ^ (2 : Nat)
        = 4 * Real.pi ^ (2 : Nat) * mp.m ^ (2 : Nat) * a ^ (2 : Nat) * b ^ (2 : Nat) := hmul_sq
    _ = ((4 * Real.pi ^ (2 : Nat) * mp.m / gp.mu) * a ^ (3 : Nat)) *
          ‖L0‖ ^ (2 : Nat) := by rw [htarget_mul]

theorem kepler_third_law_of_configurationPeriod
    (mp : MassParam) (gp : GravitationalParam) (gamma : Real -> PhaseSpace)
    (hgamma : IsSolution mp gp gamma) (hH : energy mp gp (gamma 0) < 0)
    (hL : angularMomentum (gamma 0) ≠ 0) {T : Real}
    (hT : HasConfigurationPeriod mp gp gamma T) :
    T ^ (2 : Nat) =
      (4 * Real.pi ^ (2 : Nat) * mp.m / gp.mu) *
        (semiMajorAxis mp gp (gamma 0)) ^ (3 : Nat) := by
  exact kepler_third_law_of_period_and_area mp gp gamma hgamma hH hL hT
    (configurationPeriod_sweptArea_eq_pi_mul_semiAxes mp gp gamma hgamma hH hL hT)

theorem kepler_third_law
    (mp : MassParam) (gp : GravitationalParam) (gamma : Real -> PhaseSpace)
    (hgamma : IsSolution mp gp gamma) (hH : energy mp gp (gamma 0) < 0)
    (hL : angularMomentum (gamma 0) ≠ 0) {T : Real}
    (hT : HasOrbitalPeriod mp gp gamma T) :
    T ^ (2 : Nat) =
      (4 * Real.pi ^ (2 : Nat) * mp.m / gp.mu) *
        (semiMajorAxis mp gp (gamma 0)) ^ (3 : Nat) := by
  exact kepler_third_law_of_configurationPeriod mp gp gamma hgamma hH hL hT.toHasConfigurationPeriod

theorem kepler_laws_from_comoment
    (mp : MassParam) (gp : GravitationalParam) (gamma : Real -> PhaseSpace) (hgamma : IsSolution mp gp gamma)
    (hH : energy mp gp (gamma 0) < 0) (hL : angularMomentum (gamma 0) ≠ 0) :
    (∀ t, radialDist (gamma t).1 > 0 ∧ inner ℝ (angularMomentum (gamma 0)) ((gamma t).1) = 0) ∧
    (let z0 := gamma 0
      let A0 := laplaceLenz mp gp z0
      let L0 := angularMomentum z0
      let e := eccentricity mp gp z0
      let a := semiMajorAxis mp gp z0
      let b := semiMinorAxis mp gp z0
      (A0 = 0 → ∀ t : Real, radialDist (gamma t).1 = a ∧ a = b) ∧
        (A0 ≠ 0 →
          ∃ eA eB : Vec3,
            inner ℝ L0 eA = 0 ∧
            inner ℝ L0 eB = 0 ∧
            inner ℝ eA eA = 1 ∧
            inner ℝ eB eB = 1 ∧
            inner ℝ eA eB = 0 ∧
            a ^ (2 : Nat) - b ^ (2 : Nat) = (a * e) ^ (2 : Nat) ∧
            (∀ t : Real,
              let q := (gamma t).1
              let x := inner ℝ eA q
              let y := inner ℝ eB q
              ((x + a * e) ^ (2 : Nat)) / (a ^ (2 : Nat)) +
                  (y ^ (2 : Nat)) / (b ^ (2 : Nat)) =
                1))) ∧
    (∀ t, signedArealVelocity mp gamma t =
      ‖angularMomentum (gamma 0)‖ / (2 * mp.m)) ∧
    (∀ {t0 t1 s0 s1 : Real}, t1 - t0 = s1 - s0 →
      sweptAreaOn mp gamma t0 t1 = sweptAreaOn mp gamma s0 s1) ∧
    (∀ {T : Real}, HasConfigurationPeriod mp gp gamma T →
      T ^ (2 : Nat) =
        (4 * Real.pi ^ (2 : Nat) * mp.m / gp.mu) *
          (semiMajorAxis mp gp (gamma 0)) ^ (3 : Nat)) := by
  constructor
  · intro t
    refine ⟨lt_of_le_of_ne (radialDist_nonneg _) (Ne.symm (hgamma.noCollision t)), ?_⟩
    exact (planarity mp gp gamma hgamma hL t).1
  · constructor
    · exact kepler_first_law_cartesian_ellipse mp gp gamma hgamma hH hL
    · constructor
      · exact kepler_second_law mp gp gamma hgamma hL
      · constructor
        · intro t0 t1 s0 s1 hspan
          exact equal_areas_in_equal_times mp gp gamma hgamma hL hspan
        · intro T hT
          exact kepler_third_law_of_configurationPeriod mp gp gamma hgamma hH hL hT

theorem kepler_laws_from_comoment_source
    (mp : MassParam) (gp : GravitationalParam) (gamma : Real -> PhaseSpace)
    (hgamma : IsSolution mp gp gamma) (hH : energy mp gp (gamma 0) < 0)
    (hL : angularMomentum (gamma 0) ≠ 0) :
    (∀ u v w : Vec3, ∀ z : PhaseSpace,
      poissonBracket (X_u v) (L_u u) z = X_u (cross v u) z ∧
      poissonBracket (P_u v) (L_u u) z = P_u (cross v u) z ∧
      poissonBracket (L_u u) (L_u w) z = L_u (cross u w) z ∧
      poissonBracket (L_u u) (keplerHamiltonian mp gp) z = 0) ∧
    (∀ h : Real, h < 0 →
      ∀ uv uv' : Vec3 × Vec3, ∀ z : NegativeEnergyShell mp gp h,
        poissonBracket (mu_h mp gp h uv) (mu_h mp gp h uv') z.1 =
          mu_h mp gp h (so4ModelBracket uv uv') z.1) ∧
    (let z0 := gamma 0
      let A0 := laplaceLenz mp gp z0
      let L0 := angularMomentum z0
      let e := eccentricity mp gp z0
      let l := semiLatusRectum mp gp z0
      let a := semiMajorAxis mp gp z0
      let b := semiMinorAxis mp gp z0
      (∀ t : Real, inner ℝ L0 (gamma t).1 = 0) ∧
        e = ‖A0‖ / (mp.m * gp.mu) ∧
        l = ‖L0‖ ^ (2 : Nat) / (mp.m * gp.mu) ∧
        a = -(gp.mu / (2 * energy mp gp z0)) ∧
        0 ≤ e ∧ e < 1 ∧ 0 < a ∧ 0 < b ∧
        (A0 = 0 → ∀ t : Real, radialDist (gamma t).1 = a) ∧
        (A0 ≠ 0 →
          ∃ eA eB : Vec3,
            inner ℝ L0 eA = 0 ∧
            inner ℝ L0 eB = 0 ∧
            inner ℝ eA eA = 1 ∧
            inner ℝ eB eB = 1 ∧
            inner ℝ eA eB = 0 ∧
            Real.sqrt (a ^ (2 : Nat) - b ^ (2 : Nat)) = a * e ∧
            (-a * e) + Real.sqrt (a ^ (2 : Nat) - b ^ (2 : Nat)) = 0 ∧
            (-a * e) - Real.sqrt (a ^ (2 : Nat) - b ^ (2 : Nat)) = -2 * a * e ∧
            ∀ t : Real,
              let q := (gamma t).1
              let x := inner ℝ eA q
              let y := inner ℝ eB q
              ((x + a * e) ^ (2 : Nat)) / (a ^ (2 : Nat)) +
                  (y ^ (2 : Nat)) / (b ^ (2 : Nat)) =
                1)) ∧
    ((∀ t : Real,
      signedArealVelocity mp gamma t =
        ‖angularMomentum (gamma 0)‖ / (2 * mp.m)) ∧
      (∀ {t0 t1 s0 s1 : Real}, t1 - t0 = s1 - s0 →
        sweptAreaOn mp gamma t0 t1 = sweptAreaOn mp gamma s0 s1)) ∧
    (∀ {T : Real}, HasConfigurationPeriod mp gp gamma T →
      T ^ (2 : Nat) =
        (4 * Real.pi ^ (2 : Nat) * mp.m / gp.mu) *
          (semiMajorAxis mp gp (gamma 0)) ^ (3 : Nat)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro u v w z
    exact rotational_comoment mp gp u v w z
  · intro h hh uv uv' z
    exact hidden_so4_comoment mp gp h uv uv' z hh
  · exact kepler_first_law_source mp gp gamma hgamma hH hL
  · exact kepler_second_law_source mp gp gamma hgamma hL
  · intro T hT
    exact kepler_third_law_of_configurationPeriod mp gp gamma hgamma hH hL hT

end

end Kepler
