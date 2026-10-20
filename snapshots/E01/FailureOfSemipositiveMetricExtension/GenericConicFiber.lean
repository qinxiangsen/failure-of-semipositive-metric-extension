import FailureOfSemipositiveMetricExtension.GenericConicExceptional

/-! Exact classification of each nonsingular pencil fibre by the actual
projective-line parametrization, with exceptional points included. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.NearbyPencil.Conic
noncomputable section
open Set Topology
open scoped Manifold ContDiff

theorem pencilMap_awayVector (t : ℂ) (p : Fiber t) (w : Fin 3 → ℂ)
    (hw : w ≠ 0)
    (hp : FixedFiber.blowdown t p = Projectivization.mk ℂ w hw)
    (haway : ∀ r, FixedFiber.blowdown t p ≠ centre r t) :
    pencilMap t p = ProjectiveLine.vectorPoint (PencilSections.homogeneousPencil t (w 0) (w 1) (w 2)) := by
  obtain ⟨d,hd⟩ := GlobalLineBundle.divisionPatch_cover (FixedFiber.inclusion t p)
  let i := GlobalLineBundle.divisionFrame d
  let v := ProjectivePlane.vector i.1 (ProjectivePlane.coordinates i.1 (FixedFiber.blowdown t p))
  have hi : p ∈ FixedFiberBundle.baseSet t i := hd.2
  have hnorm : Projectivization.mk ℂ v (ProjectivePlane.vector_nonzero i.1 _) =
      Projectivization.mk ℂ w hw :=
    (ProjectivePlane.param_coordinates i.1 _ hi.1).trans hp
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp hnorm
  have ha0 : a ≠ 0 := by
    intro h
    have hz : v = 0 := by simpa [h] using ha.symm
    exact ProjectivePlane.vector_nonzero i.1 _ hz
  have haway : FixedFiber.inclusion t p ∈ GlobalIncidence.awayCentres := by
    intro r
    change FixedFiber.blowdown t p ≠ centre r t
    exact haway r
  let E := GlobalLineBundle.exceptionalProduct.coefficient i (FixedFiber.inclusion t p)
  have hE : E ≠ 0 := GlobalLineBundle.exceptionalProduct_coefficient_ne_zero _ haway i hi
  have hn : E • localVector t i p = PencilSections.homogeneousPencil t (v 0) (v 1) (v 2) := by
    ext k
    change E * (GlobalLineBundle.liftedPencil k).coefficient i (FixedFiber.inclusion t p) = _
    rw [GlobalLineBundle.liftedPencil_coefficient k d _ hd]
    have h := GlobalLineBundle.pencilLocalQuotient_identity k d (FixedFiber.inclusion t p) hd
    calc
      _ = (GlobalLineBundle.pulledBackPencil k).coefficient i (FixedFiber.inclusion t p) := by
        rw [mul_comm]; exact h
      _ = _ := by fin_cases k <;> rfl
  have hv : PencilSections.homogeneousPencil t (v 0) (v 1) (v 2) =
      a^2 • PencilSections.homogeneousPencil t (w 0) (w 1) (w 2) := by
    rw [← ha]
    ext k
    fin_cases k <;> simp [PencilSections.homogeneousPencil,Coordinates.F₁,Coordinates.F₂] <;> ring
  rw [pencilMap_local t i p hi,← ProjectiveLine.vectorPoint_smul E hE,hn,hv,
    ProjectiveLine.vectorPoint_smul _ (pow_ne_zero 2 ha0)]


def centreSourceVector (c : Data) (r : Fin 4) : Blowup.Plane :=
  match r with
  | 0 => ![1,0]
  | 1 => ![0,1]
  | 2 => ![1,1]
  | 3 => ![c.a,c.b]

theorem centreSourceVector_ne_zero (c : Data) (r : Fin 4) : centreSourceVector c r ≠ 0 := by
  intro h
  fin_cases r
  · have hh := congrFun h 0; simpa [centreSourceVector] using hh
  · have hh := congrFun h 1; simpa [centreSourceVector] using hh
  · have hh := congrFun h 0; simpa [centreSourceVector] using hh
  · exact c.a_ne_zero (congrFun h 0)

def centreParameter (c : Data) (r : Fin 4) : Direction :=
  Projectivization.mk ℂ (centreSourceVector c r) (centreSourceVector_ne_zero c r)

theorem base_centreParameter (c : Data) (r : Fin 4) :
    base c (centreParameter c r) = centre r c.t := by
  rw [centreParameter,base_mk,← centre_mk]
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  let a : ℂ := match r with
    | 0 => c.b
    | 1 => -c.a
    | 2 => c.b-c.a
    | 3 => c.t*c.a*c.b*(c.b-c.a)
  refine ⟨a,?_⟩
  fin_cases r <;> ext k <;> fin_cases k <;>
    simp [a,baseVector,denominator,centreSourceVector,centreVector,
      Coordinates.p₁,Coordinates.p₂,Coordinates.p₃,Coordinates.p₄] <;> ring <;> simp

/-- Every exceptional point in this pencil fibre is already present in the
explicit projective-line image. -/
theorem pencilFiber_centre (c : Data) (p : Fiber c.t) (r : Fin 4)
    (hp : FixedFiber.blowdown c.t p = centre r c.t) (hf : pencilMap c.t p = pencilValue c) :
    param c (centreParameter c r) = p := by
  apply pencilMap_injective_on_centre c.t c.t_ne_zero r
    (param c (centreParameter c r)) p (base_centreParameter c r) hp
  rw [pencilMap_param,hf]

/-- Away from the four centres, the pencil equation reconstructs the exact
homogeneous quadratic parametrization, and incidence uniqueness fixes every direction. -/
theorem pencilFiber_away (c : Data) (p : Fiber c.t)
    (haway : ∀ r, FixedFiber.blowdown c.t p ≠ centre r c.t)
    (hf : pencilMap c.t p = pencilValue c) : p ∈ Set.range (param c) := by
  let w := (FixedFiber.blowdown c.t p).rep
  have hw : w ≠ 0 := (FixedFiber.blowdown c.t p).rep_nonzero
  have hp : FixedFiber.blowdown c.t p = Projectivization.mk ℂ w hw := (Projectivization.mk_rep _).symm
  let P := PencilSections.homogeneousPencil c.t (w 0) (w 1) (w 2)
  have hP : P ≠ 0 := by
    intro hzero
    have hvan : ∀ k, (GlobalLineBundle.pencilHomogeneous k).value (c.t,w) = 0 := by
      intro k
      have hh := congrFun hzero k
      fin_cases k <;> exact hh
    obtain ⟨r,hr⟩ := GlobalLineBundle.pencilHomogeneous_common_zero c.t c.t_ne_zero w hw hvan
    exact haway r (hp.trans hr)
  have hab : (![c.a,c.b] : Blowup.Plane) ≠ 0 := by
    intro h; exact c.a_ne_zero (congrFun h 0)
  have he : ProjectiveLine.vectorPoint P = ProjectiveLine.vectorPoint ![c.a,c.b] :=
    (pencilMap_awayVector c.t p w hw hp haway).symm.trans hf
  rw [ProjectiveLine.vectorPoint_eq_mk P hP,ProjectiveLine.vectorPoint_eq_mk _ hab] at he
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp he
  have ha0 : a ≠ 0 := by
    intro h
    exact hP (by simpa [h] using ha.symm)
  have h0 : Coordinates.F₁ c.t (w 0) (w 1) (w 2) = a*c.a := (congrFun ha 0).symm
  have h1 : Coordinates.F₂ c.t (w 0) (w 1) (w 2) = a*c.b := (congrFun ha 1).symm
  have hgood : GoodVector c.t w := by
    change _ ≠ 0 ∧ _ ≠ 0 ∧ _ ≠ 0
    rw [h0,h1,← mul_sub]
    exact ⟨mul_ne_zero ha0 c.a_ne_zero,mul_ne_zero ha0 c.b_ne_zero,mul_ne_zero ha0 c.sub_ne_zero⟩
  have heq : c.t*w 0*w 1*(c.b-c.a) = w 2*(c.b*w 0-c.a*w 1) := by
    have hz : c.b*Coordinates.F₁ c.t (w 0) (w 1) (w 2) -
        c.a*Coordinates.F₂ c.t (w 0) (w 1) (w 2) = 0 := by rw [h0,h1]; ring
    dsimp [Coordinates.F₁,Coordinates.F₂] at hz
    linear_combination -hz
  have hQ : denominator c ![w 0,w 1] • w = baseVector c ![w 0,w 1] := by
    ext k
    fin_cases k
    · simp [baseVector,denominator,mul_comm]
    · simp [baseVector,denominator,mul_comm]
    · simpa [baseVector,denominator,mul_comm] using heq.symm
  let d := Projectivization.mk ℂ ![w 0,w 1] (goodVector_xy_ne_zero c.t w hgood)
  have hb : FixedFiber.blowdown c.t (param c d) = FixedFiber.blowdown c.t p := by
    change base c d = _
    rw [show d = Projectivization.mk ℂ ![w 0,w 1] (goodVector_xy_ne_zero c.t w hgood) from rfl,base_mk,hp]
    exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨denominator c ![w 0,w 1],hQ⟩
  refine ⟨d,?_⟩
  apply Subtype.ext
  apply Prod.ext hb
  funext r
  apply directions_eq_away (FixedFiber.inclusion c.t (param c d)) (FixedFiber.inclusion c.t p) r hb rfl
  change FixedFiber.blowdown c.t (param c d) ≠ centre r c.t
  rw [hb]
  exact haway r

/-- Exact equality with the full actual pencil fibre, including all exceptional points. -/
theorem range_param (c : Data) : Set.range (param c) = {p | pencilMap c.t p = pencilValue c} := by
  ext p
  constructor
  · rintro ⟨d,rfl⟩; exact pencilMap_param c d
  · intro hp
    by_cases hc : ∃ r, FixedFiber.blowdown c.t p = centre r c.t
    · obtain ⟨r,hr⟩ := hc
      exact ⟨centreParameter c r,pencilFiber_centre c p r hr hp⟩
    · exact pencilFiber_away c p (by simpa only [not_exists] using hc) hp

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.NearbyPencil.Conic
