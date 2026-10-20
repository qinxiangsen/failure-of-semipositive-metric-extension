import FailureOfSemipositiveMetricExtension.FixedFiberSectionDataOfMap
import FailureOfSemipositiveMetricExtension.AdjointSectionIntegrability

/-! Arbitrary actual adjoint sections and actual weighted multiplier germs.
The canonical-factor unit is retained in the precise stalk equation, and the
membership equivalence is proved in every actual scalar frame. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle IsManifold Manifold Topology TopologicalSpace CategoryTheory Opposite
open scoped Manifold ContDiff

def adjointMapCoefficient (m : ℕ) (s : ∀ p : Fiber 0, (adjointCore 0 m).Fiber p)
    (d : DivisionIndex) (p : Fiber 0) : ℂ := ((adjointCore 0 m).localTriv d ⟨p,s p⟩).2

theorem adjointMapCoefficient_contMDiffOn (m : ℕ)
    (s : ∀ p : Fiber 0, (adjointCore 0 m).Fiber p)
    (hs : ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (fun p => (⟨p,s p⟩ : (adjointCore 0 m).TotalSpace))) (d : DivisionIndex) :
    ContMDiffOn 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) ω (adjointMapCoefficient m s d) (divisionPatch 0 d) := by
  let e := (adjointCore 0 m).localTriv d
  haveI : MemTrivializationAtlas e := ⟨⟨d,rfl⟩⟩
  exact contMDiff_snd.comp_contMDiffOn (e.contMDiffOn.comp hs.contMDiffOn (fun p hp => hp))

def adjointMapCoefficientSection (m : ℕ)
    (s : ∀ p : Fiber 0, (adjointCore 0 m).Fiber p)
    (hs : ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (fun p => (⟨p,s p⟩ : (adjointCore 0 m).TotalSpace))) (d : DivisionIndex) :
    C^∞⟮𝓘(ℂ,FixedFiber.Coord),divisionOpen d;𝓘(ℂ),ℂ⟯ :=
  functionSectionOn (divisionOpen d) (adjointMapCoefficient m s d)
    (adjointMapCoefficient_contMDiffOn m s hs d)

def adjointMapGerm (m : ℕ)
    (s : ∀ p : Fiber 0, (adjointCore 0 m).Fiber p)
    (hs : ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (fun p => (⟨p,s p⟩ : (adjointCore 0 m).TotalSpace)))
    (d : DivisionIndex) (p : Fiber 0) (hp : p ∈ divisionPatch 0 d) : HolomorphicStalk 0 p :=
  (holomorphicSheaf 0).presheaf.germ (divisionOpen d) p hp (adjointMapCoefficientSection m s hs d)

theorem adjointMapGerm_factorization (m : ℕ)
    (s : ∀ p : Fiber 0, (adjointCore 0 m).Fiber p)
    (hs : ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (fun p => (⟨p,s p⟩ : (adjointCore 0 m).TotalSpace)))
    (d : DivisionIndex) (p : Fiber 0) (hp : p ∈ divisionPatch 0 d) :
    adjointMapGerm m s hs d p hp = canonicalFactorGerm d p hp *
      sectionGerm (ambientDataOfAdjointMap 0 m s hs) (divisionFrame d) p hp.2 := by
  rw [sectionGerm_eq_restrict (ambientDataOfAdjointMap 0 m s hs) (divisionFrame d) p hp.2
    (divisionOpen d) (divisionPatch_subset_frame 0 d) hp]
  unfold adjointMapGerm canonicalFactorGerm
  rw [← map_mul]
  congr 1
  apply Subtype.ext
  funext q
  exact ambientDataOfAdjointMap_coefficient 0 m s hs d q q.2

theorem adjointMapGerm_mem_ellPower_iff (m k : ℕ)
    (s : ∀ p : Fiber 0, (adjointCore 0 m).Fiber p)
    (hs : ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (fun p => (⟨p,s p⟩ : (adjointCore 0 m).TotalSpace)))
    (d : DivisionIndex) (p : Fiber 0) (hp : p ∈ divisionPatch 0 d) :
    adjointMapGerm m s hs d p hp ∈ ellPowerStalkIdeal k p ↔
      sectionGerm (ambientDataOfAdjointMap 0 m s hs) (divisionFrame d) p hp.2 ∈ ellPowerStalkIdeal k p := by
  rw [adjointMapGerm_factorization]
  exact Ideal.unit_mul_mem_iff_mem _ (canonicalFactorGerm_isUnit d p hp)

theorem adjointMapGerm_all_frames_iff (m k : ℕ)
    (s : ∀ p : Fiber 0, (adjointCore 0 m).Fiber p)
    (hs : ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (fun p => (⟨p,s p⟩ : (adjointCore 0 m).TotalSpace))) :
    (∀ d p hp, adjointMapGerm m s hs d p hp ∈ ellPowerStalkIdeal k p) ↔
      (∀ i p hp, sectionGerm (ambientDataOfAdjointMap 0 m s hs) i p hp ∈ ellPowerStalkIdeal k p) := by
  constructor
  · intro h i p hp
    let d := canonicalPatchAt 0 p
    have hd := canonicalPatchAt_mem 0 p
    have hm := (adjointMapGerm_mem_ellPower_iff m k s hs d p hd).mp (h d p hd)
    rw [← sectionGerm_transition (ambientDataOfAdjointMap 0 m s hs) (divisionFrame d) i p ⟨hd.2,hp⟩]
    exact (ellPowerStalkIdeal k p).mul_mem_left _ hm
  · intro h d p hp
    exact (adjointMapGerm_mem_ellPower_iff m k s hs d p hp).mpr (h _ _ hp.2)

/-- The restricted multiplier condition on every actual canonical/line frame. -/
def HasCentralIntegrableGerms (m : ℕ)
    (s : ∀ p : Fiber 0, (adjointCore 0 m).Fiber p)
    (hs : ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (fun p => (⟨p,s p⟩ : (adjointCore 0 m).TotalSpace))) : Prop :=
  ∀ d p hp, FailureOfSemipositiveMetricExtension.Multiplier.IntegrableGerm (Fiber 0) m
    (centralH0.weight (divisionFrame d)) p (adjointMapGerm m s hs d p hp)

/-- The only multiplier-theoretic input is the existing precise smooth-divisor
SNC germ theorem, via centralH0_multiplierGerm_iff. The bundle comparison is proved. -/
theorem central_integrable_germs_iff_ambient_ellPower (m : ℕ)
    (s : ∀ p : Fiber 0, (adjointCore 0 m).Fiber p)
    (hs : ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (fun p => (⟨p,s p⟩ : (adjointCore 0 m).TotalSpace))) :
    HasCentralIntegrableGerms m s hs ↔
      ∀ i p hp, sectionGerm (ambientDataOfAdjointMap 0 m s hs) i p hp ∈ ellPowerStalkIdeal (m/2) p := by
  rw [← adjointMapGerm_all_frames_iff m (m/2) s hs]
  apply forall_congr'
  intro d
  apply forall_congr'
  intro p
  apply forall_congr'
  intro hp
  exact centralH0_multiplierGerm_iff m (divisionFrame d) p hp.2 _

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
