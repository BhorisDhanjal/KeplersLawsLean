import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.LinearAlgebra.CrossProduct

namespace Kepler

noncomputable section

abbrev Vec3 := EuclideanSpace Real (Fin 3)
abbrev PhaseSpace := Vec3 × Vec3

structure MassParam where
  m : Real
  hm : 0 < m

structure GravitationalParam where
  mu : Real
  hmu : 0 < mu

def cross (u w : Vec3) : Vec3 :=
  WithLp.toLp (2 : ENNReal) ((crossProduct (fun i => u i)) (fun i => w i))

def angularMomentum (qp : PhaseSpace) : Vec3 :=
  cross qp.1 qp.2

def energy (mp : MassParam) (gp : GravitationalParam) (qp : PhaseSpace) : Real :=
  (1 / (2 * mp.m)) * (norm qp.2) ^ (2 : Nat) - gp.mu / (norm qp.1)

def radialDist (q : Vec3) : Real :=
  norm q

abbrev NoncollisionPhaseSpace := { z : PhaseSpace // radialDist z.1 ≠ 0 }

def laplaceLenz (mp : MassParam) (gp : GravitationalParam) (qp : PhaseSpace) : Vec3 :=
  cross qp.2 (cross qp.1 qp.2) - ((mp.m * gp.mu) / norm qp.1) • qp.1

lemma radialDist_nonneg (q : Vec3) : 0 ≤ radialDist q := by
  simp [radialDist]

lemma radialDist_eq_zero_iff (q : Vec3) : radialDist q = 0 ↔ q = 0 := by
  simp [radialDist]

lemma radialDist_zero : radialDist (0 : Vec3) = 0 := by
  simp [radialDist]

instance : Coe NoncollisionPhaseSpace PhaseSpace := ⟨Subtype.val⟩

lemma NoncollisionPhaseSpace.radialDist_ne_zero (z : NoncollisionPhaseSpace) :
    radialDist ((z : PhaseSpace).1) ≠ 0 := by
  exact z.2

lemma cross_self (u : Vec3) : cross u u = 0 := by
  simp [cross]

lemma angularMomentum_self_zero (q : Vec3) : angularMomentum (q, q) = 0 := by
  simp [angularMomentum, cross_self]

end

end Kepler
