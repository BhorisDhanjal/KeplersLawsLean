import Kepler.Definitions
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear

set_option linter.style.longLine false

namespace Kepler

noncomputable section

def keplerVectorField (mp : MassParam) (gp : GravitationalParam) (qp : PhaseSpace) : PhaseSpace := 
  let q := qp.1
  let p := qp.2
  let r := norm q
  let force : Vec3 := 
    if _hr : r = 0 then 
      0 
    else 
      WithLp.toLp (2 : ENNReal) (fun i => (-gp.mu / r ^ (3 : Nat)) * q i)
  ((1 / mp.m) • p, force)

lemma keplerVectorField_fst (mp : MassParam) (gp : GravitationalParam) (qp : PhaseSpace) : 
    (keplerVectorField mp gp qp).1 = (1 / mp.m) • qp.2 := by 
  rfl

lemma keplerVectorField_snd_of_radialDist_ne_zero
    (mp : MassParam) (gp : GravitationalParam) (qp : PhaseSpace) (h : radialDist qp.1 ≠ 0) :
    (keplerVectorField mp gp qp).2 =
      WithLp.toLp (2 : ENNReal) (fun i => (-gp.mu / (radialDist qp.1) ^ (3 : Nat)) * qp.1 i) := by
  have hnorm : norm qp.1 ≠ 0 := by
    simpa [radialDist] using h
  simp [keplerVectorField, radialDist, hnorm]

lemma keplerVectorField_snd_eq_smul_of_radialDist_ne_zero
    (mp : MassParam) (gp : GravitationalParam) (qp : PhaseSpace) (h : radialDist qp.1 ≠ 0) :
    (keplerVectorField mp gp qp).2 =
      (-gp.mu / (radialDist qp.1) ^ (3 : Nat)) • qp.1 := by
  ext i
  rw [keplerVectorField_snd_of_radialDist_ne_zero mp gp qp h]
  simp

lemma cross_pos_with_keplerForce_eq_zero_of_radialDist_ne_zero
    (mp : MassParam) (gp : GravitationalParam) (qp : PhaseSpace) (h : radialDist qp.1 ≠ 0) :
    cross qp.1 (keplerVectorField mp gp qp).2 = 0 := by
  rw [keplerVectorField_snd_of_radialDist_ne_zero mp gp qp h]
  ext i
  fin_cases i <;> simp [cross, cross_apply, mul_assoc, mul_left_comm, mul_comm]

lemma inner_fin3 (u v : Vec3) :
    inner ℝ u v = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 := by
  calc
    inner ℝ u v = v.ofLp ⬝ᵥ star u.ofLp := by
      simpa using (EuclideanSpace.inner_eq_star_dotProduct (x := u) (y := v))
    _ = v.ofLp 0 * star (u.ofLp 0) + v.ofLp 1 * star (u.ofLp 1) + v.ofLp 2 * star (u.ofLp 2) := by
      simp [dotProduct, Fin.sum_univ_three, add_assoc]
    _ = v.ofLp 0 * u.ofLp 0 + v.ofLp 1 * u.ofLp 1 + v.ofLp 2 * u.ofLp 2 := by
      simp
    _ = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 := by
      ring

structure IsSolution (mp : MassParam) (gp : GravitationalParam) (gamma : Real -> PhaseSpace) : Prop where
  ode :
    ∀ t : Real, HasDerivAt gamma (keplerVectorField mp gp (gamma t)) t
  noCollision :
    ∀ t : Real, radialDist (gamma t).1 ≠ 0

lemma IsSolution.position_rhs
    {mp : MassParam} {gp : GravitationalParam} {gamma : Real -> PhaseSpace}
    (hgamma : IsSolution mp gp gamma) (t : Real) :
    (keplerVectorField mp gp (gamma t)).1 = (1 / mp.m) • (gamma t).2 := by
  have hode := hgamma.ode t
  simpa using keplerVectorField_fst mp gp (gamma t)

lemma IsSolution.momentum_rhs_eq_smul_position
    {mp : MassParam} {gp : GravitationalParam} {gamma : Real -> PhaseSpace}
    (hgamma : IsSolution mp gp gamma) (t : Real) :
    (keplerVectorField mp gp (gamma t)).2 =
      (-gp.mu / (radialDist (gamma t).1) ^ (3 : Nat)) • (gamma t).1 := by
  exact
    keplerVectorField_snd_eq_smul_of_radialDist_ne_zero mp gp (gamma t) (hgamma.noCollision t)

lemma IsSolution.position_cross_momentum_rhs_eq_zero
    {mp : MassParam} {gp : GravitationalParam} {gamma : Real -> PhaseSpace}
    (hgamma : IsSolution mp gp gamma) (t : Real) :
    cross (gamma t).1 (keplerVectorField mp gp (gamma t)).2 = 0 := by
  exact
    cross_pos_with_keplerForce_eq_zero_of_radialDist_ne_zero mp gp (gamma t) (hgamma.noCollision t)

lemma IsSolution.hasDerivAt_position_coord
    {mp : MassParam} {gp : GravitationalParam} {gamma : Real -> PhaseSpace}
    (hgamma : IsSolution mp gp gamma) (t : Real) (i : Fin 3) :
    HasDerivAt (fun τ : Real => (gamma τ).1 i) ((gamma t).2 i / mp.m) t := by
  let posCoord : PhaseSpace →L[ℝ] ℝ := 
    (EuclideanSpace.proj (𝕜 := Real) i).comp (ContinuousLinearMap.fst ℝ Vec3 Vec3)
  have hpos :
      HasDerivAt (fun τ : Real => posCoord (gamma τ))
        (posCoord (keplerVectorField mp gp (gamma t))) t := by
    exact posCoord.hasFDerivAt.comp_hasDerivAt t (hgamma.ode t)
  simpa [posCoord, hgamma.position_rhs t, smul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm,
    mul_assoc] using hpos

lemma IsSolution.hasDerivAt_momentum_coord
    {mp : MassParam} {gp : GravitationalParam} {gamma : Real -> PhaseSpace}
    (hgamma : IsSolution mp gp gamma) (t : Real) (i : Fin 3) :
    HasDerivAt (fun τ : Real => (gamma τ).2 i) ((keplerVectorField mp gp (gamma t)).2 i) t := by
  let momCoord : PhaseSpace →L[ℝ] ℝ := 
    (EuclideanSpace.proj (𝕜 := Real) i).comp (ContinuousLinearMap.snd ℝ Vec3 Vec3)
  have hmom :
      HasDerivAt (fun τ : Real => momCoord (gamma τ))
        (momCoord (keplerVectorField mp gp (gamma t))) t := by
    exact momCoord.hasFDerivAt.comp_hasDerivAt t (hgamma.ode t)
  simpa [momCoord] using hmom

end

end Kepler
