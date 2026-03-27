import Kepler.Dynamics
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option linter.style.longLine false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

namespace Kepler

lemma inner_cross_self (u v : Vec3) : inner ℝ u (cross u v) = 0 := by
  simp [inner_fin3, cross, cross_apply]
  ring

lemma cross_q_cross_qp (q p : Vec3) :
    cross q (cross q p) = (inner ℝ q p) • q - (radialDist q) ^ (2 : Nat) • p := by
  have hnorm_sq : (radialDist q) ^ (2 : Nat) = q 0 ^ (2 : Nat) + q 1 ^ (2 : Nat) + q 2 ^ (2 : Nat) := by
    simpa [radialDist, Fin.sum_univ_three] using (EuclideanSpace.real_norm_sq_eq (n := Fin 3) q)
  rw [inner_fin3 q p]
  ext i
  fin_cases i <;> simp [cross, cross_apply, hnorm_sq]
  · ring
  · ring
  · ring

lemma cross_smul_left (a : Real) (q p : Vec3) :
    cross (a • q) p = a • cross q p := by
  ext i
  fin_cases i <;> simp [cross, cross_apply]
  · ring
  · ring
  · ring

lemma IsSolution.hasDerivAt_angularMomentum_coord
    {mp : MassParam} {gp : GravitationalParam} {gamma : Real -> PhaseSpace}
    (hgamma : IsSolution mp gp gamma) (t : Real) (i : Fin 3) :
    HasDerivAt (fun tau : Real => angularMomentum (gamma tau) i) 0 t := by
  fin_cases i
  · have hq1 := hgamma.hasDerivAt_position_coord t 1
    have hq2 := hgamma.hasDerivAt_position_coord t 2
    have hp1 := hgamma.hasDerivAt_momentum_coord t 1
    have hp2 := hgamma.hasDerivAt_momentum_coord t 2
    have hderiv :
        HasDerivAt
          (fun tau : Real => angularMomentum (gamma tau) 0)
          (((gamma t).2 1 / mp.m) * (gamma t).2 2 + (gamma t).1 1 * (keplerVectorField mp gp (gamma t)).2 2 -
            (((gamma t).2 2 / mp.m) * (gamma t).2 1 + (gamma t).1 2 * (keplerVectorField mp gp (gamma t)).2 1))
          t := by
      simpa [angularMomentum, cross, cross_apply, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
        mul_assoc, mul_left_comm, mul_comm] using (hq1.mul hp2).sub (hq2.mul hp1)
    have hforce :
        (gamma t).1 1 * (keplerVectorField mp gp (gamma t)).2 2 -
          (gamma t).1 2 * (keplerVectorField mp gp (gamma t)).2 1 = 0 := by
      simpa [cross, cross_apply] using
        congrArg (fun v : Vec3 => v 0) (hgamma.position_cross_momentum_rhs_eq_zero t)
    have hvalue :
        ((gamma t).2 1 / mp.m) * (gamma t).2 2 + (gamma t).1 1 * (keplerVectorField mp gp (gamma t)).2 2 -
            (((gamma t).2 2 / mp.m) * (gamma t).2 1 + (gamma t).1 2 * (keplerVectorField mp gp (gamma t)).2 1) =
          0 := by
      have hpair :
          ((gamma t).2 1 / mp.m) * (gamma t).2 2 - ((gamma t).2 2 / mp.m) * (gamma t).2 1 = 0 := by
        ring
      calc
        ((gamma t).2 1 / mp.m) * (gamma t).2 2 + (gamma t).1 1 * (keplerVectorField mp gp (gamma t)).2 2 -
            (((gamma t).2 2 / mp.m) * (gamma t).2 1 + (gamma t).1 2 * (keplerVectorField mp gp (gamma t)).2 1)
            =
          (((gamma t).2 1 / mp.m) * (gamma t).2 2 - ((gamma t).2 2 / mp.m) * (gamma t).2 1) +
            ((gamma t).1 1 * (keplerVectorField mp gp (gamma t)).2 2 -
              (gamma t).1 2 * (keplerVectorField mp gp (gamma t)).2 1) := by
              ring
        _ = 0 + 0 := by simp [hforce, hpair]
        _ = 0 := by ring
    exact hvalue ▸ hderiv
  · have hq0 := hgamma.hasDerivAt_position_coord t 0
    have hq2 := hgamma.hasDerivAt_position_coord t 2
    have hp0 := hgamma.hasDerivAt_momentum_coord t 0
    have hp2 := hgamma.hasDerivAt_momentum_coord t 2
    have hderiv :
        HasDerivAt
          (fun tau : Real => angularMomentum (gamma tau) 1)
          (((gamma t).2 2 / mp.m) * (gamma t).2 0 + (gamma t).1 2 * (keplerVectorField mp gp (gamma t)).2 0 -
            (((gamma t).2 0 / mp.m) * (gamma t).2 2 + (gamma t).1 0 * (keplerVectorField mp gp (gamma t)).2 2))
          t := by
      simpa [angularMomentum, cross, cross_apply, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
        mul_assoc, mul_left_comm, mul_comm] using (hq2.mul hp0).sub (hq0.mul hp2)
    have hforce :
        (gamma t).1 2 * (keplerVectorField mp gp (gamma t)).2 0 -
          (gamma t).1 0 * (keplerVectorField mp gp (gamma t)).2 2 = 0 := by
      simpa [cross, cross_apply] using
        congrArg (fun v : Vec3 => v 1) (hgamma.position_cross_momentum_rhs_eq_zero t)
    have hvalue :
        ((gamma t).2 2 / mp.m) * (gamma t).2 0 + (gamma t).1 2 * (keplerVectorField mp gp (gamma t)).2 0 -
            (((gamma t).2 0 / mp.m) * (gamma t).2 2 + (gamma t).1 0 * (keplerVectorField mp gp (gamma t)).2 2) =
          0 := by
      have hpair :
          ((gamma t).2 2 / mp.m) * (gamma t).2 0 - ((gamma t).2 0 / mp.m) * (gamma t).2 2 = 0 := by
        ring
      calc
        ((gamma t).2 2 / mp.m) * (gamma t).2 0 + (gamma t).1 2 * (keplerVectorField mp gp (gamma t)).2 0 -
            (((gamma t).2 0 / mp.m) * (gamma t).2 2 + (gamma t).1 0 * (keplerVectorField mp gp (gamma t)).2 2)
            =
          (((gamma t).2 2 / mp.m) * (gamma t).2 0 - ((gamma t).2 0 / mp.m) * (gamma t).2 2) +
            ((gamma t).1 2 * (keplerVectorField mp gp (gamma t)).2 0 -
              (gamma t).1 0 * (keplerVectorField mp gp (gamma t)).2 2) := by
              ring
        _ = 0 + 0 := by simp [hforce, hpair]
        _ = 0 := by ring
    exact hvalue ▸ hderiv
  · have hq0 := hgamma.hasDerivAt_position_coord t 0
    have hq1 := hgamma.hasDerivAt_position_coord t 1
    have hp0 := hgamma.hasDerivAt_momentum_coord t 0
    have hp1 := hgamma.hasDerivAt_momentum_coord t 1
    have hderiv :
        HasDerivAt
          (fun tau : Real => angularMomentum (gamma tau) 2)
          (((gamma t).2 0 / mp.m) * (gamma t).2 1 + (gamma t).1 0 * (keplerVectorField mp gp (gamma t)).2 1 -
            (((gamma t).2 1 / mp.m) * (gamma t).2 0 + (gamma t).1 1 * (keplerVectorField mp gp (gamma t)).2 0))
          t := by
      simpa [angularMomentum, cross, cross_apply, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
        mul_assoc, mul_left_comm, mul_comm] using (hq0.mul hp1).sub (hq1.mul hp0)
    have hforce :
        (gamma t).1 0 * (keplerVectorField mp gp (gamma t)).2 1 -
          (gamma t).1 1 * (keplerVectorField mp gp (gamma t)).2 0 = 0 := by
      simpa [cross, cross_apply] using
        congrArg (fun v : Vec3 => v 2) (hgamma.position_cross_momentum_rhs_eq_zero t)
    have hvalue :
        ((gamma t).2 0 / mp.m) * (gamma t).2 1 + (gamma t).1 0 * (keplerVectorField mp gp (gamma t)).2 1 -
            (((gamma t).2 1 / mp.m) * (gamma t).2 0 + (gamma t).1 1 * (keplerVectorField mp gp (gamma t)).2 0) =
          0 := by
      have hpair :
          ((gamma t).2 0 / mp.m) * (gamma t).2 1 - ((gamma t).2 1 / mp.m) * (gamma t).2 0 = 0 := by
        ring
      calc
        ((gamma t).2 0 / mp.m) * (gamma t).2 1 + (gamma t).1 0 * (keplerVectorField mp gp (gamma t)).2 1 -
            (((gamma t).2 1 / mp.m) * (gamma t).2 0 + (gamma t).1 1 * (keplerVectorField mp gp (gamma t)).2 0)
            =
          (((gamma t).2 0 / mp.m) * (gamma t).2 1 - ((gamma t).2 1 / mp.m) * (gamma t).2 0) +
            ((gamma t).1 0 * (keplerVectorField mp gp (gamma t)).2 1 -
              (gamma t).1 1 * (keplerVectorField mp gp (gamma t)).2 0) := by
              ring
        _ = 0 + 0 := by simp [hforce, hpair]
        _ = 0 := by ring
    exact hvalue ▸ hderiv

lemma IsSolution.hasDerivAt_cross_momentum_angularMomentum
    {mp : MassParam} {gp : GravitationalParam} {gamma : Real -> PhaseSpace}
    (hgamma : IsSolution mp gp gamma) (t : Real) :
    HasDerivAt (fun tau : Real => cross (gamma tau).2 (angularMomentum (gamma tau)))
      (cross (keplerVectorField mp gp (gamma t)).2 (angularMomentum (gamma t))) t := by
  have hcoord : forall i : Fin 3,
      HasDerivAt (fun tau : Real => (cross (gamma tau).2 (angularMomentum (gamma tau))) i)
        ((cross (keplerVectorField mp gp (gamma t)).2 (angularMomentum (gamma t))) i) t := by
    intro i
    fin_cases i
    · have hp1 := hgamma.hasDerivAt_momentum_coord t 1
      have hp2 := hgamma.hasDerivAt_momentum_coord t 2
      have hL1 := hgamma.hasDerivAt_angularMomentum_coord t 1
      have hL2 := hgamma.hasDerivAt_angularMomentum_coord t 2
      convert (hp1.mul hL2).sub (hp2.mul hL1) using 1
      · simp [cross, cross_apply]
    · have hp0 := hgamma.hasDerivAt_momentum_coord t 0
      have hp2 := hgamma.hasDerivAt_momentum_coord t 2
      have hL0 := hgamma.hasDerivAt_angularMomentum_coord t 0
      have hL2 := hgamma.hasDerivAt_angularMomentum_coord t 2
      convert (hp2.mul hL0).sub (hp0.mul hL2) using 1
      · simp [cross, cross_apply]
    · have hp0 := hgamma.hasDerivAt_momentum_coord t 0
      have hp1 := hgamma.hasDerivAt_momentum_coord t 1
      have hL0 := hgamma.hasDerivAt_angularMomentum_coord t 0
      have hL1 := hgamma.hasDerivAt_angularMomentum_coord t 1
      convert (hp0.mul hL1).sub (hp1.mul hL0) using 1
      · simp [cross, cross_apply]
  let e : Vec3 ≃L[ℝ] (Fin 3 -> Real) := EuclideanSpace.equiv (ι := Fin 3) (𝕜 := Real)
  have hpi : HasDerivAt (fun tau : Real => e (cross (gamma tau).2 (angularMomentum (gamma tau))))
      (e (cross (keplerVectorField mp gp (gamma t)).2 (angularMomentum (gamma t)))) t := by
    rw [hasDerivAt_pi]
    intro i
    simpa [e] using hcoord i
  have hback : HasDerivAt
      (fun tau : Real => e.symm (e (cross (gamma tau).2 (angularMomentum (gamma tau)))))
      (e.symm (e (cross (keplerVectorField mp gp (gamma t)).2 (angularMomentum (gamma t))))) t := by
    exact e.symm.hasFDerivAt.comp_hasDerivAt t hpi
  simpa [e] using hback

lemma IsSolution.hasDerivAt_mu_div_radial
    {mp : MassParam} {gp : GravitationalParam} {gamma : Real -> PhaseSpace}
    (hgamma : IsSolution mp gp gamma) (t : Real) :
    HasDerivAt (fun tau : Real => (mp.m * gp.mu) / radialDist ((gamma tau).1))
      (-(gp.mu * (inner ℝ (gamma t).1 (gamma t).2 / (radialDist ((gamma t).1)) ^ (3 : Nat)))) t := by
  let pos : Real -> Vec3 := fun tau => (gamma tau).1
  let fstCLM : PhaseSpace →L[ℝ] Vec3 := ContinuousLinearMap.fst ℝ Vec3 Vec3
  have hpos :
      HasDerivAt pos ((1 / mp.m) • (gamma t).2) t := by
    have hfst :
        HasDerivAt (fun tau : Real => fstCLM (gamma tau))
          (fstCLM (keplerVectorField mp gp (gamma t))) t := by
      exact fstCLM.hasFDerivAt.comp_hasDerivAt t (hgamma.ode t)
    simpa [pos, fstCLM, hgamma.position_rhs t] using hfst
  have hnorm_sq :
      HasDerivAt (fun tau : Real => radialDist (pos tau) ^ (2 : Nat))
        (2 * inner ℝ (pos t) ((1 / mp.m) • (gamma t).2)) t := by
    simpa [pos, radialDist] using hpos.norm_sq
  have hrad :
      HasDerivAt (fun tau : Real => radialDist (pos tau))
        (inner ℝ (pos t) ((1 / mp.m) • (gamma t).2) / radialDist (pos t)) t := by
    have hsqrt := hnorm_sq.sqrt (by simpa [pos] using pow_ne_zero 2 (hgamma.noCollision t))
    convert hsqrt using 1
    · funext tau
      simp [pos, radialDist, pow_two]
    · field_simp [hgamma.noCollision t]
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (radialDist_nonneg (pos t))]
  have hinv :
      HasDerivAt (fun tau : Real => (radialDist (pos tau))⁻¹)
        (-(inner ℝ (pos t) ((1 / mp.m) • (gamma t).2) / radialDist (pos t)) / radialDist (pos t) ^ (2 : Nat))
        t := by
    exact hrad.inv (by simpa [pos] using hgamma.noCollision t)
  have hcoef :
      HasDerivAt (fun tau : Real => (mp.m * gp.mu) * (radialDist (pos tau))⁻¹)
        ((mp.m * gp.mu) *
          (-(inner ℝ (pos t) ((1 / mp.m) • (gamma t).2) / radialDist (pos t)) / radialDist (pos t) ^ (2 : Nat)))
        t := by
    simpa using hinv.const_mul (mp.m * gp.mu)
  have hcoef' :
      HasDerivAt (fun tau : Real => (mp.m * gp.mu) / radialDist ((gamma tau).1))
        ((mp.m * gp.mu) *
          (-(inner ℝ (pos t) ((1 / mp.m) • (gamma t).2) / radialDist (pos t)) / radialDist (pos t) ^ (2 : Nat)))
        t := by
    simpa [pos, div_eq_mul_inv] using hcoef
  have hm0 : mp.m ≠ 0 := ne_of_gt mp.hm
  have hvalue :
      (mp.m * gp.mu) *
          (-(inner ℝ (pos t) ((1 / mp.m) • (gamma t).2) / radialDist (pos t)) / radialDist (pos t) ^ (2 : Nat)) =
        -(gp.mu * (inner ℝ (gamma t).1 (gamma t).2 / (radialDist ((gamma t).1)) ^ (3 : Nat))) := by
    simp only [pos, real_inner_smul_right]
    field_simp [hm0, hgamma.noCollision t]
  exact hvalue.symm ▸ hcoef'

lemma IsSolution.hasDerivAt_scaled_position
    {mp : MassParam} {gp : GravitationalParam} {gamma : Real -> PhaseSpace}
    (hgamma : IsSolution mp gp gamma) (t : Real) :
    HasDerivAt (fun tau : Real => ((mp.m * gp.mu) / radialDist ((gamma tau).1)) • (gamma tau).1)
      ((-(gp.mu * (inner ℝ (gamma t).1 (gamma t).2 / (radialDist ((gamma t).1)) ^ (3 : Nat)))) •
          (gamma t).1 +
        (gp.mu / radialDist ((gamma t).1)) • (gamma t).2) t := by
  let pos : Real -> Vec3 := fun tau => (gamma tau).1
  let fstCLM : PhaseSpace →L[ℝ] Vec3 := ContinuousLinearMap.fst ℝ Vec3 Vec3
  have hpos :
      HasDerivAt pos ((1 / mp.m) • (gamma t).2) t := by
    have hfst :
        HasDerivAt (fun tau : Real => fstCLM (gamma tau))
          (fstCLM (keplerVectorField mp gp (gamma t))) t := by
      exact fstCLM.hasFDerivAt.comp_hasDerivAt t (hgamma.ode t)
    simpa [pos, fstCLM, hgamma.position_rhs t] using hfst
  have hcoef := hgamma.hasDerivAt_mu_div_radial t
  have hm0 : mp.m ≠ 0 := ne_of_gt mp.hm
  have hscaled :
      HasDerivAt (fun tau : Real => ((mp.m * gp.mu) / radialDist ((gamma tau).1)) • (gamma tau).1)
        ((-(gp.mu * (inner ℝ (gamma t).1 (gamma t).2 / (radialDist ((gamma t).1)) ^ (3 : Nat)))) • pos t +
          ((mp.m * gp.mu) / radialDist ((gamma t).1)) • ((1 / mp.m) • (gamma t).2))
        t := by
    simpa [pos, add_assoc, add_left_comm, add_comm] using hcoef.smul hpos
  have hvalue :
      (-(gp.mu * (inner ℝ (gamma t).1 (gamma t).2 / (radialDist ((gamma t).1)) ^ (3 : Nat)))) • pos t +
          ((mp.m * gp.mu) / radialDist ((gamma t).1)) • ((1 / mp.m) • (gamma t).2) =
        (-(gp.mu * (inner ℝ (gamma t).1 (gamma t).2 / (radialDist ((gamma t).1)) ^ (3 : Nat)))) •
            (gamma t).1 +
          (gp.mu / radialDist ((gamma t).1)) • (gamma t).2 := by
    have hmul :
        ((mp.m * gp.mu) / radialDist ((gamma t).1)) * mp.m⁻¹ = gp.mu / radialDist ((gamma t).1) := by
      field_simp [hm0, hgamma.noCollision t]
    ext i
    calc
      ((-(gp.mu * (inner ℝ (gamma t).1 (gamma t).2 / (radialDist ((gamma t).1)) ^ (3 : Nat)))) • pos t +
            ((mp.m * gp.mu) / radialDist ((gamma t).1)) • ((1 / mp.m) • (gamma t).2)) i
          =
        (-(gp.mu * (inner ℝ (gamma t).1 (gamma t).2 / (radialDist ((gamma t).1)) ^ (3 : Nat)))) *
            pos t i +
          (((mp.m * gp.mu) / radialDist ((gamma t).1)) * mp.m⁻¹) * (gamma t).2 i := by
            simp [smul_smul, one_div]
      _ =
        (-(gp.mu * (inner ℝ (gamma t).1 (gamma t).2 / (radialDist ((gamma t).1)) ^ (3 : Nat)))) *
            pos t i +
          (gp.mu / radialDist ((gamma t).1)) * (gamma t).2 i := by rw [hmul]
      _ =
        ((-(gp.mu * (inner ℝ (gamma t).1 (gamma t).2 / (radialDist ((gamma t).1)) ^ (3 : Nat)))) •
              (gamma t).1 +
            (gp.mu / radialDist ((gamma t).1)) • (gamma t).2) i := by
              simp [pos]
  exact hvalue ▸ hscaled

lemma IsSolution.hasDerivAt_laplaceLenz_coord
    {mp : MassParam} {gp : GravitationalParam} {gamma : Real -> PhaseSpace}
    (hgamma : IsSolution mp gp gamma) (t : Real) (i : Fin 3) :
    HasDerivAt (fun tau : Real => laplaceLenz mp gp (gamma tau) i) 0 t := by
  have hF : HasDerivAt (fun tau : Real => cross (gamma tau).2 (angularMomentum (gamma tau)))
      (cross (keplerVectorField mp gp (gamma t)).2 (angularMomentum (gamma t))) t := by
    exact hgamma.hasDerivAt_cross_momentum_angularMomentum t
  have hU : HasDerivAt (fun tau : Real => ((mp.m * gp.mu) / radialDist ((gamma tau).1)) • (gamma tau).1)
      ((-(gp.mu * (inner ℝ (gamma t).1 (gamma t).2 / (radialDist ((gamma t).1)) ^ (3 : Nat)))) •
          (gamma t).1 +
        (gp.mu / radialDist ((gamma t).1)) • (gamma t).2) t := by
    exact hgamma.hasDerivAt_scaled_position t
  have htarget :
      cross (keplerVectorField mp gp (gamma t)).2 (angularMomentum (gamma t)) =
        (-(gp.mu * (inner ℝ (gamma t).1 (gamma t).2 / (radialDist ((gamma t).1)) ^ (3 : Nat)))) •
            (gamma t).1 +
          (gp.mu / radialDist ((gamma t).1)) • (gamma t).2 := by
    rw [hgamma.momentum_rhs_eq_smul_position t, angularMomentum, cross_smul_left, cross_q_cross_qp]
    ext j
    simp [smul_sub, smul_smul]
    field_simp [hgamma.noCollision t]
    ring
  let coord : Vec3 →L[ℝ] ℝ := EuclideanSpace.proj (𝕜 := Real) i
  have hdiff :
      HasDerivAt (fun tau : Real =>
          cross (gamma tau).2 (angularMomentum (gamma tau)) -
            ((mp.m * gp.mu) / radialDist ((gamma tau).1)) • (gamma tau).1)
        (cross (keplerVectorField mp gp (gamma t)).2 (angularMomentum (gamma t)) -
          ((-(gp.mu * (inner ℝ (gamma t).1 (gamma t).2 / (radialDist ((gamma t).1)) ^ (3 : Nat)))) •
              (gamma t).1 +
            (gp.mu / radialDist ((gamma t).1)) • (gamma t).2))
        t := by
    exact hF.sub hU
  have hvec :
      HasDerivAt (fun tau : Real => laplaceLenz mp gp (gamma tau)) 0 t := by
    have hzero :
        cross (keplerVectorField mp gp (gamma t)).2 (angularMomentum (gamma t)) -
          ((-(gp.mu * (inner ℝ (gamma t).1 (gamma t).2 / (radialDist ((gamma t).1)) ^ (3 : Nat)))) •
              (gamma t).1 +
            (gp.mu / radialDist ((gamma t).1)) • (gamma t).2) =
          0 := by
      simp [htarget]
    exact hzero ▸ (by simpa [laplaceLenz] using hdiff)
  have hcoord :
      HasDerivAt
        (fun tau : Real => coord (laplaceLenz mp gp (gamma tau)))
        (coord 0) t := by
    exact coord.hasFDerivAt.comp_hasDerivAt t hvec
  simpa [coord, laplaceLenz] using hcoord

lemma laplaceLenz_const
    {mp : MassParam} {gp : GravitationalParam} {gamma : Real -> PhaseSpace}
    (hgamma : IsSolution mp gp gamma) (t : Real) :
    laplaceLenz mp gp (gamma t) = laplaceLenz mp gp (gamma 0) := by
  ext i
  exact is_const_of_deriv_eq_zero
    (fun s : Real => (hgamma.hasDerivAt_laplaceLenz_coord s i).differentiableAt)
    (fun s : Real => by simpa using (hgamma.hasDerivAt_laplaceLenz_coord s i).deriv)
    t 0

theorem basic_identities_L_A
    (mp : MassParam) (gp : GravitationalParam) (z : PhaseSpace) (h : radialDist z.1 ≠ 0) :
    inner ℝ (angularMomentum z) (laplaceLenz mp gp z) = 0 ∧
    (∃ a b : Real, laplaceLenz mp gp z = a • z.1 + b • z.2) ∧
    inner ℝ (laplaceLenz mp gp z) z.1 =
      ‖angularMomentum z‖ ^ (2 : Nat) - (mp.m * gp.mu) * radialDist z.1 ∧
    ‖laplaceLenz mp gp z‖ ^ (2 : Nat) =
      (mp.m * gp.mu) ^ (2 : Nat) +
        2 * mp.m * energy mp gp z * ‖angularMomentum z‖ ^ (2 : Nat) := by
  set q : Vec3 := z.1
  set p : Vec3 := z.2
  set L : Vec3 := angularMomentum z
  set A : Vec3 := laplaceLenz mp gp z
  set mu : Real := mp.m * gp.mu
  have hnormp_sq :
      ‖p‖ ^ (2 : Nat) = p 0 ^ (2 : Nat) + p 1 ^ (2 : Nat) + p 2 ^ (2 : Nat) := by
    simpa [Fin.sum_univ_three] using (EuclideanSpace.real_norm_sq_eq (n := Fin 3) p)
  have hnormL_sq :
      ‖L‖ ^ (2 : Nat) = L 0 ^ (2 : Nat) + L 1 ^ (2 : Nat) + L 2 ^ (2 : Nat) := by
    simpa [Fin.sum_univ_three] using (EuclideanSpace.real_norm_sq_eq (n := Fin 3) L)
  have hp_cross_qp :
      cross p (cross q p) = ‖p‖ ^ (2 : Nat) • q - (inner ℝ q p) • p := by
    rw [inner_fin3 q p, hnormp_sq]
    ext i
    fin_cases i <;> simp [cross, cross_apply]
    · ring
    · ring
    · ring
  have hAunit :
      A = cross p L - mu • ((1 / radialDist q) • q) := by
    simp [A, L, q, p, mu, laplaceLenz, angularMomentum, radialDist, smul_smul, div_eq_mul_inv]
  have hAdecomp :
      A = (‖p‖ ^ (2 : Nat) - mu / radialDist q) • q - (inner ℝ q p) • p := by
    calc
      A = cross p (cross q p) - (mu / radialDist q) • q := by
            calc
              A = cross p L - mu • ((1 / radialDist q) • q) := hAunit
              _ = cross p (cross q p) - (mu / radialDist q) • q := by
                    simp [L, q, p, angularMomentum, mu, radialDist, smul_smul, div_eq_mul_inv]
      _ = ‖p‖ ^ (2 : Nat) • q - (inner ℝ q p) • p - (mu / radialDist q) • q := by
            rw [hp_cross_qp]
      _ = (‖p‖ ^ (2 : Nat) - mu / radialDist q) • q - (inner ℝ q p) • p := by
            ext i
            fin_cases i <;> simp
            · ring
            · ring
            · ring
  have hspan : ∃ a b : Real, A = a • q + b • p := by
    refine ⟨‖p‖ ^ (2 : Nat) - mu / radialDist q, -(inner ℝ q p), ?_⟩
    simpa [sub_eq_add_neg] using hAdecomp
  have hdot (u v : Vec3) : (fun i => u i) ⬝ᵥ (fun i => v i) = inner ℝ u v := by
    rw [inner_fin3]
    simp [dotProduct, Fin.sum_univ_three, add_assoc]
  have hpL : inner ℝ p L = 0 := by
    rw [← hdot p L]
    simpa [L, q, p, angularMomentum, cross] using
      (dot_cross_self (fun i => q i) (fun i => p i))
  have hLq : inner ℝ L q = 0 := by
    rw [real_inner_comm, ← hdot q L]
    simpa [L, q, p, angularMomentum, cross] using
      (dot_self_cross (fun i => q i) (fun i => p i))
  have hLp : inner ℝ L p = 0 := by
    simpa [real_inner_comm] using hpL
  have hLA : inner ℝ L A = 0 := by
    rw [hAdecomp, inner_sub_right, real_inner_smul_right, real_inner_smul_right, hLq, hLp]
    ring
  have htriple_perm (u v w : Vec3) :
      inner ℝ (cross u v) w = inner ℝ v (cross w u) := by
    rw [← hdot (cross u v) w, ← hdot v (cross w u)]
    simpa [cross, dotProduct_comm] using
      (triple_product_permutation (fun i => v i) (fun i => w i) (fun i => u i)).symm
  have hcross_pL_q : inner ℝ (cross p L) q = ‖L‖ ^ (2 : Nat) := by
    calc
      inner ℝ (cross p L) q = inner ℝ L (cross q p) := by
        simpa using htriple_perm p L q
      _ = inner ℝ L L := by
        simp [L, q, p, angularMomentum]
      _ = ‖L‖ ^ (2 : Nat) := by
        rw [real_inner_self_eq_norm_sq]
  have hqnorm : ‖q‖ ≠ 0 := by
    simpa [q, radialDist] using h
  have hunit_q : inner ℝ ((1 / radialDist q) • q) q = radialDist q := by
    calc
      inner ℝ ((1 / radialDist q) • q) q = (1 / radialDist q) * inner ℝ q q := by
            rw [real_inner_smul_left]
      _ = (1 / radialDist q) * (radialDist q) ^ (2 : Nat) := by
            rw [real_inner_self_eq_norm_sq, radialDist]
      _ = radialDist q := by
            field_simp [h]
  have hAq :
      inner ℝ A q = ‖L‖ ^ (2 : Nat) - mu * radialDist q := by
    calc
      inner ℝ A q = inner ℝ (cross p L - mu • ((1 / radialDist q) • q)) q := by
        rw [hAunit]
      _ = inner ℝ (cross p L) q - inner ℝ (mu • ((1 / radialDist q) • q)) q := by
        rw [inner_sub_left]
      _ = inner ℝ (cross p L) q - mu * inner ℝ ((1 / radialDist q) • q) q := by
        rw [real_inner_smul_left]
      _ = ‖L‖ ^ (2 : Nat) - mu * radialDist q := by
        rw [hcross_pL_q, hunit_q]
  have hunit_sq : inner ℝ ((1 / radialDist q) • q) ((1 / radialDist q) • q) = 1 := by
    calc
      inner ℝ ((1 / radialDist q) • q) ((1 / radialDist q) • q) =
          (1 / radialDist q) * ((1 / radialDist q) * inner ℝ q q) := by
            rw [real_inner_smul_left, real_inner_smul_right]
      _ = (1 / radialDist q) * (1 / radialDist q) * inner ℝ q q := by
            rw [mul_assoc]
      _ = (1 / radialDist q) * (1 / radialDist q) * (radialDist q) ^ (2 : Nat) := by
            rw [real_inner_self_eq_norm_sq, radialDist]
      _ = 1 := by
            field_simp [h]
  have hcrossterm :
      inner ℝ (cross p L) ((1 / radialDist q) • q) = ‖L‖ ^ (2 : Nat) / radialDist q := by
    rw [real_inner_smul_right, hcross_pL_q]
    ring
  have hcrossterm' :
      inner ℝ ((1 / radialDist q) • q) (cross p L) = ‖L‖ ^ (2 : Nat) / radialDist q := by
    rw [real_inner_comm]
    exact hcrossterm
  have hcrossnorm :
      ‖cross p L‖ ^ (2 : Nat) = ‖p‖ ^ (2 : Nat) * ‖L‖ ^ (2 : Nat) := by
    calc
      ‖cross p L‖ ^ (2 : Nat) = inner ℝ (cross p L) (cross p L) := by
        rw [real_inner_self_eq_norm_sq]
      _ = inner ℝ p p * inner ℝ L L - inner ℝ p L * inner ℝ L p := by
        rw [← hdot (cross p L) (cross p L), ← hdot p p, ← hdot L L, ← hdot p L, ← hdot L p]
        simpa [cross] using
          (cross_dot_cross (fun i => p i) (fun i => L i) (fun i => p i) (fun i => L i))
      _ = ‖p‖ ^ (2 : Nat) * ‖L‖ ^ (2 : Nat) := by
        rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hpL, hLp]
        ring
  have henergy :
      2 * mp.m * energy mp gp z = ‖p‖ ^ (2 : Nat) - 2 * mu / radialDist q := by
    have hm0 : mp.m ≠ 0 := ne_of_gt mp.hm
    calc
      2 * mp.m * energy mp gp z =
          2 * mp.m * ((1 / (2 * mp.m)) * ‖p‖ ^ (2 : Nat) - gp.mu / radialDist q) := by
            simp [energy, q, p, radialDist]
      _ = ‖p‖ ^ (2 : Nat) - 2 * mu / radialDist q := by
            field_simp [mu, hm0, h]
            ring
  have hAnorm :
      ‖A‖ ^ (2 : Nat) = mu ^ (2 : Nat) + 2 * mp.m * energy mp gp z * ‖L‖ ^ (2 : Nat) := by
    calc
      ‖A‖ ^ (2 : Nat) = inner ℝ A A := by
        rw [real_inner_self_eq_norm_sq]
      _ =
          inner ℝ (cross p L - mu • ((1 / radialDist q) • q))
            (cross p L - mu • ((1 / radialDist q) • q)) := by
              rw [hAunit]
      _ =
          inner ℝ (cross p L) (cross p L) -
            mu * inner ℝ (cross p L) ((1 / radialDist q) • q) -
            mu * inner ℝ ((1 / radialDist q) • q) (cross p L) +
            mu * mu * inner ℝ ((1 / radialDist q) • q) ((1 / radialDist q) • q) := by
              rw [inner_sub_left, inner_sub_right, inner_sub_right]
              rw [real_inner_smul_right, real_inner_smul_left, real_inner_smul_left,
                real_inner_smul_left, real_inner_smul_right, real_inner_smul_right]
              ring
      _ = ‖cross p L‖ ^ (2 : Nat) - 2 * mu * (‖L‖ ^ (2 : Nat) / radialDist q) + mu ^ (2 : Nat) := by
            rw [real_inner_self_eq_norm_sq, hcrossterm, hcrossterm', hunit_sq]
            ring
      _ = ‖p‖ ^ (2 : Nat) * ‖L‖ ^ (2 : Nat) - 2 * mu * (‖L‖ ^ (2 : Nat) / radialDist q) + mu ^ (2 : Nat) := by
            rw [hcrossnorm]
      _ = mu ^ (2 : Nat) + (‖p‖ ^ (2 : Nat) - 2 * mu / radialDist q) * ‖L‖ ^ (2 : Nat) := by
            ring
      _ = mu ^ (2 : Nat) + 2 * mp.m * energy mp gp z * ‖L‖ ^ (2 : Nat) := by
            rw [henergy]
  constructor
  · simpa [L, A] using hLA
  constructor
  · simpa [A, q, p] using hspan
  constructor
  · simpa [A, L, q, mu] using hAq
  · simpa [A, L, mu] using hAnorm

lemma angularMomentum_const
    {mp : MassParam} {gp : GravitationalParam} {gamma : Real -> PhaseSpace}
    (hgamma : IsSolution mp gp gamma) (t : Real) :
    angularMomentum (gamma t) = angularMomentum (gamma 0) := by
  ext i
  exact is_const_of_deriv_eq_zero
    (fun s : Real => (hgamma.hasDerivAt_angularMomentum_coord s i).differentiableAt)
    (fun s : Real => by simpa using (hgamma.hasDerivAt_angularMomentum_coord s i).deriv)
    t 0

lemma energy_const
    {mp : MassParam} {gp : GravitationalParam} {gamma : Real -> PhaseSpace}
    (hgamma : IsSolution mp gp gamma) (t : Real) :
    energy mp gp (gamma t) = energy mp gp (gamma 0) := by
  have henergy :
      ∀ s : Real, HasDerivAt (fun tau : Real => energy mp gp (gamma tau)) 0 s := by
    intro s
    let sndCLM : PhaseSpace →L[ℝ] Vec3 := ContinuousLinearMap.snd ℝ Vec3 Vec3
    have hmom :
        HasDerivAt (fun tau : Real => sndCLM (gamma tau))
          (sndCLM (keplerVectorField mp gp (gamma s))) s := by
      exact sndCLM.hasFDerivAt.comp_hasDerivAt s (hgamma.ode s)
    have hp :
        HasDerivAt (fun tau : Real => (gamma tau).2)
          ((keplerVectorField mp gp (gamma s)).2) s := by
      simpa [sndCLM] using hmom
    have hkin' :
        HasDerivAt
          (fun tau : Real => (1 / (2 * mp.m)) * radialDist ((gamma tau).2) ^ (2 : Nat))
          ((1 / (2 * mp.m)) * (2 * inner ℝ (gamma s).2 (keplerVectorField mp gp (gamma s)).2))
          s := by
      simpa [radialDist] using hp.norm_sq.const_mul (1 / (2 * mp.m))
    have hkinValue :
        (1 / (2 * mp.m)) * (2 * inner ℝ (gamma s).2 (keplerVectorField mp gp (gamma s)).2) =
          (1 / mp.m) * inner ℝ (gamma s).2 (keplerVectorField mp gp (gamma s)).2 := by
      ring_nf
    have hkin :
        HasDerivAt
          (fun tau : Real => (1 / (2 * mp.m)) * radialDist ((gamma tau).2) ^ (2 : Nat))
          ((1 / mp.m) * inner ℝ (gamma s).2 (keplerVectorField mp gp (gamma s)).2)
          s := by
      exact hkinValue.symm ▸ hkin'
    have hpot :
        HasDerivAt
          (fun tau : Real => (1 / mp.m) * (((mp.m * gp.mu) / radialDist ((gamma tau).1)))
          )
          ((1 / mp.m) * (-(gp.mu * (inner ℝ (gamma s).1 (gamma s).2 / (radialDist ((gamma s).1)) ^ (3 : Nat)))))
          s := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (hgamma.hasDerivAt_mu_div_radial s).const_mul (1 / mp.m)
    have hsum :
        HasDerivAt
          (fun tau : Real =>
            (1 / (2 * mp.m)) * radialDist ((gamma tau).2) ^ (2 : Nat) -
              (1 / mp.m) * ((mp.m * gp.mu) / radialDist ((gamma tau).1)))
          ((1 / mp.m) * inner ℝ (gamma s).2 (keplerVectorField mp gp (gamma s)).2 -
            ((1 / mp.m) *
              (-(gp.mu * (inner ℝ (gamma s).1 (gamma s).2 / (radialDist ((gamma s).1)) ^ (3 : Nat)))))
            ) s := by
      exact hkin.sub hpot
    have hsum' :
        HasDerivAt (fun tau : Real => energy mp gp (gamma tau))
          ((1 / mp.m) * inner ℝ (gamma s).2 (keplerVectorField mp gp (gamma s)).2 -
            ((1 / mp.m) *
              (-(gp.mu * (inner ℝ (gamma s).1 (gamma s).2 / (radialDist ((gamma s).1)) ^ (3 : Nat)))))
            ) s := by
      convert hsum using 1
      · funext tau
        rw [energy, radialDist]
        field_simp [ne_of_gt mp.hm, hgamma.noCollision tau]
        have hcancel :
            (2 * mp.m * gp.mu / ‖(gamma tau).1‖) * radialDist ((gamma tau).1) =
              2 * mp.m * gp.mu := by
          calc
            (2 * mp.m * gp.mu / ‖(gamma tau).1‖) * radialDist ((gamma tau).1)
                = 2 * mp.m * gp.mu * (‖(gamma tau).1‖⁻¹ * ‖(gamma tau).1‖) := by
                    rw [radialDist, div_eq_mul_inv]
                    ring
            _ = 2 * mp.m * gp.mu * 1 := by
                    have hnorm : ‖(gamma tau).1‖⁻¹ * ‖(gamma tau).1‖ = 1 := by
                      exact inv_mul_cancel₀ (by simpa [radialDist] using hgamma.noCollision tau)
                    simp [hnorm]
            _ = 2 * mp.m * gp.mu := by
                    ring
        calc
          (‖(gamma tau).2‖ ^ 2 - 2 * mp.m * gp.mu / ‖(gamma tau).1‖) * radialDist ((gamma tau).1)
              =
            ‖(gamma tau).2‖ ^ 2 * radialDist ((gamma tau).1) -
              (2 * mp.m * gp.mu / ‖(gamma tau).1‖) * radialDist ((gamma tau).1) := by
                ring
          _ = ‖(gamma tau).2‖ ^ 2 * radialDist ((gamma tau).1) - 2 * mp.m * gp.mu := by
                rw [hcancel]
    have hzero :
        (1 / mp.m) * inner ℝ (gamma s).2 (keplerVectorField mp gp (gamma s)).2 -
            ((1 / mp.m) *
              (-(gp.mu * (inner ℝ (gamma s).1 (gamma s).2 / (radialDist ((gamma s).1)) ^ (3 : Nat))))) =
          0 := by
      rw [hgamma.momentum_rhs_eq_smul_position s]
      simp [real_inner_smul_right, real_inner_comm]
      field_simp [ne_of_gt mp.hm, hgamma.noCollision s]
      ring
    exact hzero ▸ hsum'
  exact is_const_of_deriv_eq_zero
    (fun s : Real => (henergy s).differentiableAt)
    (fun s : Real => by simpa using (henergy s).deriv)
    t 0

end Kepler
