import FailureOfSemipositiveMetricExtension.HisamotoBlowupComparison
import FailureOfSemipositiveMetricExtension.HisamotoNormalBundle
import FailureOfSemipositiveMetricExtension.HisamotoMetricPullback

/-! Actual complete ruling fibres, their projective-line homeomorphism, and
open product-disc neighbourhoods of the whole fibre. -/
namespace FailureOfSemipositiveMetricExtension.Hisamoto
noncomputable section
open Set Topology Metric
open scoped Manifold ContDiff

instance instT2SpacePoint : T2Space Point :=
  inferInstanceAs (T2Space {q : PlanePoint × Direction // Incidence q.1 q.2})

/-- The genuine inverse image of a projective ruling direction. -/
def Fibre (d : Direction) := {q : Point // ruling q = d}

instance fibre_topologicalSpace (d : Direction) : TopologicalSpace (Fibre d) :=
  inferInstanceAs (TopologicalSpace {q : Point // ruling q = d})

def fibreEquiv (i : Fin 2) (t : ℂ) : Direction ≃ Fibre (ProjectiveLine.param i t) where
  toFun p := ⟨localParam i (p,t),rfl⟩
  invFun q := fiberDirection i (blowdown q.val)
  left_inv p := fiberDirection_fiberPlane i t p
  right_inv q := by
    apply Subtype.ext
    have hq : q.val ∈ rulingChart i := ⟨t,q.property.symm⟩
    have he := localParam_localCoordinates i q.val hq
    simpa only [localCoordinates,q.property,ProjectiveLine.coordinates_param] using he

/-- Both topologies are the existing projective/incidence subspace topologies. -/
def fibreHomeomorph (i : Fin 2) (t : ℂ) : Direction ≃ₜ Fibre (ProjectiveLine.param i t) where
  toEquiv := fibreEquiv i t
  continuous_toFun := ((localParam_continuous i).comp (continuous_id.prodMk continuous_const)).subtype_mk _
  continuous_invFun := by
    apply continuous_iff_continuousAt.mpr
    intro q
    have hq : q.val ∈ rulingChart i := ⟨t,q.property.symm⟩
    change ContinuousAt (fun q : Fibre (ProjectiveLine.param i t) => fiberDirection i (blowdown q.val)) q
    have hb : Continuous (fun q : Fibre (ProjectiveLine.param i t) => blowdown q.val) :=
      blowdown_continuous.comp (show Continuous (fun q : Fibre (ProjectiveLine.param i t) => q.val) from continuous_subtype_val)
    exact (fiberDirection_contMDiffAt i 0 _ (fiberProjection_rep_nonzero i q.val hq)).continuousAt.comp (f := fun q : Fibre (ProjectiveLine.param i t) => blowdown q.val) hb.continuousAt

/-- The entire ruling fibre, including its point on E, is compact. -/
theorem fibre_compact (d : Direction) : CompactSpace (Fibre d) := by
  obtain ⟨i,t,rfl⟩ := ProjectiveLine.charts_cover d
  exact (fibreHomeomorph i t).compactSpace

/-- Its inclusion is the concrete analytic fibre parametrization used for the
actual tangent quotient and normal-bundle computation. -/
theorem fibre_param_analytic (i : Fin 2) (t : ℂ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ,Coord) ω (fun p => (fibreHomeomorph i t p).val) :=
  RulingNormal.fibreMap_contMDiff i t ω

theorem fiberPlane_zero (i : Fin 2) (t : ℂ) :
    fiberPlane i t (ProjectiveLine.param 0 0) = centre := by
  rw [fiberPlane_param_planeParam i 0 (0,t)]
  fin_cases i <;> simp [planeIndex,affinePlaneCoordinates,centre]

/-- A ruling fibre meets the actual exceptional curve at exactly one point. -/
theorem fibre_exceptional_iff (i : Fin 2) (t : ℂ) (p : Direction) :
    localParam i (p,t) ∈ exceptionalSet ↔ p = ProjectiveLine.param 0 0 := by
  change fiberPlane i t p = centre ↔ _
  rw [← fiberPlane_zero i t]
  exact (fiberPlane_injective i t).eq_iff

theorem localParam_isOpenEmbedding (i : Fin 2) : Topology.IsOpenEmbedding (localParam i) :=
  (rulingProductChart i).symm.to_isOpenEmbedding rfl

/-- The actual open neighbourhood above a round disc in a ruling base chart. -/
def discNeighbourhood (i : Fin 2) (t : ℂ) (r : ℝ) : Set Point :=
  localParam i '' ((univ : Set Direction) ×ˢ ball t r)

theorem discNeighbourhood_isOpen (i : Fin 2) (t : ℂ) (r : ℝ) : IsOpen (discNeighbourhood i t r) :=
  (localParam_isOpenEmbedding i).isOpenMap _ (isOpen_univ.prod isOpen_ball)

theorem mem_discNeighbourhood_iff (i : Fin 2) (t : ℂ) (r : ℝ) (q : Point) :
    q ∈ discNeighbourhood i t r ↔ q ∈ rulingChart i ∧ (localCoordinates i q).2 ∈ ball t r := by
  constructor
  · rintro ⟨⟨p,z⟩,hz,rfl⟩
    exact ⟨by rw [rulingChart_eq_range]; exact ⟨(p,z),rfl⟩,by simpa using hz.2⟩
  · rintro ⟨hq,hz⟩
    exact ⟨localCoordinates i q,⟨mem_univ _,hz⟩,localParam_localCoordinates i q hq⟩

theorem whole_fibre_mem_discNeighbourhood (i : Fin 2) (t : ℂ) (r : ℝ) (hr : 0 < r)
    (q : Fibre (ProjectiveLine.param i t)) : q.val ∈ discNeighbourhood i t r := by
  apply (mem_discNeighbourhood_iff i t r q.val).mpr
  exact ⟨⟨t,q.property.symm⟩,by simp [localCoordinates,q.property,hr]⟩

abbrev Disc (t : ℂ) (r : ℝ) := {z : ℂ // z ∈ ball t r}

def discProductEquiv (i : Fin 2) (t : ℂ) (r : ℝ) :
    (Direction × Disc t r) ≃ discNeighbourhood i t r where
  toFun q := ⟨localParam i (q.1,q.2.val),⟨(q.1,q.2.val),⟨mem_univ _,q.2.property⟩,rfl⟩⟩
  invFun q := ((localCoordinates i q.val).1,⟨(localCoordinates i q.val).2,
    ((mem_discNeighbourhood_iff i t r q.val).mp q.property).2⟩)
  left_inv q := by
    rcases q with ⟨p,z,hz⟩
    simp only [localCoordinates_localParam]
  right_inv q := by
    apply Subtype.ext
    exact localParam_localCoordinates i q.val (((mem_discNeighbourhood_iff i t r q.val).mp q.property).1)

/-- Actual P¹×disc neighbourhood, with both maps verified continuous. -/
def discProductHomeomorph (i : Fin 2) (t : ℂ) (r : ℝ) :
    (Direction × Disc t r) ≃ₜ discNeighbourhood i t r where
  toEquiv := discProductEquiv i t r
  continuous_toFun := ((localParam_continuous i).comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  continuous_invFun := by
    have hc : Continuous (fun q : discNeighbourhood i t r => localCoordinates i q.val) :=
      (localCoordinates_continuousOn i).comp_continuous continuous_subtype_val
        (fun q => ((mem_discNeighbourhood_iff i t r q.val).mp q.property).1)
    exact hc.fst.prodMk (hc.snd.subtype_mk _)

end
end FailureOfSemipositiveMetricExtension.Hisamoto
