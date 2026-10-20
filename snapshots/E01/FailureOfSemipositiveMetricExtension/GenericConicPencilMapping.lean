import FailureOfSemipositiveMetricExtension.GenericConicDensity

/-! Exact compatibility of the explicit conics with the actual divided pencil
map. The comparison first cancels the genuine exceptional product on the generic
locus, then uses continuity in the actual projective-line parameter. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.NearbyPencil.Conic
noncomputable section
open Set Topology
open scoped Manifold ContDiff

theorem pencilMap_goodVector (t : ℂ) (p : Fiber t) (w : Fin 3 → ℂ)
    (hw : GoodVector t w)
    (hp : FixedFiber.blowdown t p = Projectivization.mk ℂ w (goodVector_ne_zero t w hw)) :
    pencilMap t p = ProjectiveLine.vectorPoint (PencilSections.homogeneousPencil t (w 0) (w 1) (w 2)) := by
  obtain ⟨d,hd⟩ := GlobalLineBundle.divisionPatch_cover (FixedFiber.inclusion t p)
  let i := GlobalLineBundle.divisionFrame d
  let v := ProjectivePlane.vector i.1 (ProjectivePlane.coordinates i.1 (FixedFiber.blowdown t p))
  have hi : p ∈ FixedFiberBundle.baseSet t i := hd.2
  have hnorm : Projectivization.mk ℂ v (ProjectivePlane.vector_nonzero i.1 _) =
      Projectivization.mk ℂ w (goodVector_ne_zero t w hw) :=
    (ProjectivePlane.param_coordinates i.1 _ hi.1).trans hp
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp hnorm
  have ha0 : a ≠ 0 := by
    intro h
    have hz : v = 0 := by simpa [h] using ha.symm
    exact ProjectivePlane.vector_nonzero i.1 _ hz
  have haway : FixedFiber.inclusion t p ∈ GlobalIncidence.awayCentres := by
    intro r
    change FixedFiber.blowdown t p ≠ centre r t
    rw [hp]
    exact goodVector_away_centre t w hw r
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

def pencilScalar (c : Data) (v : Blowup.Plane) : ℂ :=
  c.t * v 0 * v 1 * denominator c v * (v 1-v 0)

theorem baseVector_good (c : Data) (v : Blowup.Plane) (h : pencilScalar c v ≠ 0) :
    GoodVector c.t (baseVector c v) := by
  have hp := pencil_baseVector c v
  have h0 := congrFun hp 0
  have h1 := congrFun hp 1
  change Coordinates.F₁ c.t (baseVector c v 0) (baseVector c v 1) (baseVector c v 2) = pencilScalar c v * c.a at h0
  change Coordinates.F₂ c.t (baseVector c v 0) (baseVector c v 1) (baseVector c v 2) = pencilScalar c v * c.b at h1
  change _ ≠ 0 ∧ _ ≠ 0 ∧ _ ≠ 0
  rw [h0,h1,← mul_sub]
  exact ⟨mul_ne_zero h c.a_ne_zero,mul_ne_zero h c.b_ne_zero,mul_ne_zero h c.sub_ne_zero⟩

theorem pencilMap_param_mk (c : Data) (v : Blowup.Plane) (hv : v ≠ 0) (h : pencilScalar c v ≠ 0) :
    pencilMap c.t (param c (Projectivization.mk ℂ v hv)) = pencilValue c := by
  rw [pencilMap_goodVector c.t (param c (Projectivization.mk ℂ v hv)) (baseVector c v) (baseVector_good c v h)
    (base_mk c v hv),pencil_baseVector]
  exact ProjectiveLine.vectorPoint_smul _ h _

def excludedParameters (c : Data) (e : Fin 2) : Set ℂ :=
  {0,1,if e = 0 then c.b/c.a else c.a/c.b}

theorem pencilScalar_sourceVector_ne_zero (c : Data) (e : Fin 2) (s : ℂ)
    (hs : s ∉ excludedParameters c e) : pencilScalar c (ProjectiveLine.sourceVector e s) ≠ 0 := by
  simp only [excludedParameters,Set.mem_insert_iff,Set.mem_singleton_iff,not_or] at hs
  have h0 := hs.1
  have h1 := hs.2.1
  have hroot := hs.2.2
  fin_cases e
  · change s ≠ c.b/c.a at hroot
    have hD : c.b-c.a*s ≠ 0 := by
      intro h
      apply hroot
      apply (eq_div_iff c.a_ne_zero).mpr
      linear_combination -h
    simpa [pencilScalar,denominator,ProjectiveLine.sourceVector,Blowup.vectorX] using
      mul_ne_zero (mul_ne_zero (mul_ne_zero c.t_ne_zero h0) hD) (sub_ne_zero.mpr h1)
  · change s ≠ c.a/c.b at hroot
    have hD : c.b*s-c.a ≠ 0 := by
      intro h
      apply hroot
      apply (eq_div_iff c.b_ne_zero).mpr
      linear_combination h
    simpa [pencilScalar,denominator,ProjectiveLine.sourceVector,Blowup.vectorY] using
      mul_ne_zero (mul_ne_zero (mul_ne_zero c.t_ne_zero h0) hD) (sub_ne_zero.mpr (Ne.symm h1))

/-- The entire actual projective line, including all four exceptional
intersection points, maps to the prescribed actual pencil value. -/
theorem pencilMap_param (c : Data) (d : Direction) :
    pencilMap c.t (param c d) = pencilValue c := by
  obtain ⟨e,s,rfl⟩ := ProjectiveLine.charts_cover d
  have hd : Dense {s : ℂ | s ∉ excludedParameters c e} := by
    have hf : (excludedParameters c e).Finite := by simp [excludedParameters]
    convert (dense_univ.diff_finite hf) using 1
    ext z
    simp
  have hc : Continuous (fun z : ℂ => pencilMap c.t (param c (ProjectiveLine.param e z))) :=
    (pencilMap_continuous c.t c.t_ne_zero).comp
      ((param_contMDiff c ω).continuous.comp (ProjectiveLine.param_contMDiff e ω).continuous)
  have he : (fun z : ℂ => pencilMap c.t (param c (ProjectiveLine.param e z))) =
      (fun _ => pencilValue c) := Continuous.ext_on hd hc continuous_const (by
    intro z hz
    change pencilMap c.t (param c (ProjectiveLine.param e z)) = pencilValue c
    rw [ProjectiveLine.param_eq_mk_sourceVector]
    exact pencilMap_param_mk c _ (ProjectiveLine.sourceVector_ne_zero e z)
      (pencilScalar_sourceVector_ne_zero c e z hz))
  exact congrFun he s

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.NearbyPencil.Conic
