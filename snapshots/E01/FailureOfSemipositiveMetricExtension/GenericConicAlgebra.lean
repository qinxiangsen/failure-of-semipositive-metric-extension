import FailureOfSemipositiveMetricExtension.NearbyPencilExceptionalSection

/-! Explicit homogeneous parametrizations of the generic conics in the actual
nearby pencil. All nondegeneracy conditions are displayed in the parameter data,
and all identities are verified polynomial identities. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.NearbyPencil.Conic
noncomputable section
open Set

/-- A nearby parameter and a pencil value outside the three singular values
[1:0], [0:1], and [1:1]. -/
structure Data where
  t : ℂ
  a : ℂ
  b : ℂ
  t_ne_zero : t ≠ 0
  a_ne_zero : a ≠ 0
  b_ne_zero : b ≠ 0
  sub_ne_zero : b - a ≠ 0

def denominator (c : Data) (v : Blowup.Plane) : ℂ := c.b * v 0 - c.a * v 1

/-- The degree-two blowdown vector [uD:vD:tuv(b-a)], D=bu-av. -/
def baseVector (c : Data) (v : Blowup.Plane) : Fin 3 → ℂ :=
  ![v 0 * denominator c v, v 1 * denominator c v, c.t * v 0 * v 1 * (c.b-c.a)]

/-- The four degree-one direction vectors, with the actual third-centre convention. -/
def directionMap (c : Data) (r : Fin 4) : Blowup.Plane →ₗ[ℂ] Blowup.Plane where
  toFun v := match r with
    | 0 => ![denominator c v,c.t * v 0 * (c.b-c.a)]
    | 1 => ![denominator c v,c.t * v 1 * (c.b-c.a)]
    | 2 => ![denominator c v,c.t * c.b * v 0]
    | 3 => v
  map_add' u v := by fin_cases r <;> ext j <;> fin_cases j <;> simp [denominator] <;> ring
  map_smul' a v := by fin_cases r <;> ext j <;> fin_cases j <;> simp [denominator] <;> ring

/-- Exactly the scalar factors removed from the four incidence pairs. -/
def incidenceFactor (c : Data) (r : Fin 4) (v : Blowup.Plane) : ℂ :=
  match r with
  | 0 => v 1
  | 1 => v 0
  | 2 => v 1 - v 0
  | 3 => denominator c v

theorem baseVector_smul (c : Data) (a : ℂ) (v : Blowup.Plane) :
    baseVector c (a • v) = a^2 • baseVector c v := by
  ext j
  fin_cases j <;> simp [baseVector,denominator] <;> ring

theorem baseVector_ne_zero (c : Data) (v : Blowup.Plane) (hv : v ≠ 0) : baseVector c v ≠ 0 := by
  intro hz
  have hx := congrFun hz 0
  have hy := congrFun hz 1
  have hzz := congrFun hz 2
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1
      apply hv
      ext j
      fin_cases j <;> assumption
    have hn : v 1 * (-(c.a * v 1)) ≠ 0 := mul_ne_zero h1 (neg_ne_zero.mpr (mul_ne_zero c.a_ne_zero h1))
    apply hn
    simpa [baseVector,denominator,h0] using hy
  · by_cases h1 : v 1 = 0
    · have hn : v 0 * (c.b * v 0) ≠ 0 := mul_ne_zero h0 (mul_ne_zero c.b_ne_zero h0)
      apply hn
      simpa [baseVector,denominator,h1] using hx
    · have hn : c.t * v 0 * v 1 * (c.b-c.a) ≠ 0 :=
        mul_ne_zero (mul_ne_zero (mul_ne_zero c.t_ne_zero h0) h1) c.sub_ne_zero
      exact hn (by simpa [baseVector] using hzz)

theorem directionMap_eq_zero (c : Data) (r : Fin 4) (v : Blowup.Plane)
    (h : directionMap c r v = 0) : v = 0 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  fin_cases r
  · have hu : v 0 = 0 := by
      simpa [directionMap,c.t_ne_zero,c.sub_ne_zero] using h1
    have hv : v 1 = 0 := by
      simpa [directionMap,denominator,hu,c.a_ne_zero] using h0
    ext j; fin_cases j <;> assumption
  · have hv : v 1 = 0 := by
      simpa [directionMap,c.t_ne_zero,c.sub_ne_zero] using h1
    have hu : v 0 = 0 := by
      simpa [directionMap,denominator,hv,c.b_ne_zero] using h0
    ext j; fin_cases j <;> assumption
  · have hu : v 0 = 0 := by
      simpa [directionMap,c.t_ne_zero,c.b_ne_zero] using h1
    have hv : v 1 = 0 := by
      simpa [directionMap,denominator,hu,c.a_ne_zero] using h0
    ext j; fin_cases j <;> assumption
  · exact h

theorem directionMap_injective (c : Data) (r : Fin 4) : Function.Injective (directionMap c r) := by
  intro v w h
  apply sub_eq_zero.mp
  apply directionMap_eq_zero c r
  rw [map_sub,h,sub_self]

theorem directionMap_ne_zero (c : Data) (r : Fin 4) (v : Blowup.Plane) (hv : v ≠ 0) :
    directionMap c r v ≠ 0 := fun h => hv (directionMap_eq_zero c r v h)

/-- The incidence equations include all four exceptional directions, not just
points away from the blown-up centres. -/
theorem pairMap_baseVector (c : Data) (r : Fin 4) (v : Blowup.Plane) :
    pairMap r c.t (baseVector c v) = incidenceFactor c r v • directionMap c r v := by
  fin_cases r <;> ext j <;> fin_cases j <;>
    simp [pairMap,pair,baseVector,denominator,incidenceFactor,directionMap] <;> ring

/-- The quadratic pencil evaluated on the conic is the constant pair [a:b],
with the four expected homogeneous vanishing factors made explicit. -/
theorem pencil_baseVector (c : Data) (v : Blowup.Plane) :
    PencilSections.homogeneousPencil c.t (baseVector c v 0) (baseVector c v 1) (baseVector c v 2) =
      (c.t * v 0 * v 1 * denominator c v * (v 1-v 0)) • ![c.a,c.b] := by
  ext j
  fin_cases j <;>
    simp [PencilSections.homogeneousPencil,Coordinates.F₁,Coordinates.F₂,baseVector,denominator] <;> ring

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.NearbyPencil.Conic
