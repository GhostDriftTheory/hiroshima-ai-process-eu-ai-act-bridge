import ResponsibilityOS

/-!
# EU AI Act — selected formal assurance profiles

A small application layer; the imported Responsibility OS Kernel is unchanged.
Targets: Lean/mathlib 4.26.0 and the public `ResponsibilityOS` API.

Article numbers identify *selected technical contributions*, not definitions of
legal compliance. The legal-to-formal interpretation is external to Lean.
Reference baseline: Regulation (EU) 2024/1689, original Articles 11(1), 12(1)-(2),
14(4)(d)-(e), 19(1), 43 and 72(1)-(3); consult the applicable amended text before
using the mapping for a deployment. No application dates are encoded.

Added disclosure: version keys, a logical stop/withhold gate, and a typed event
log with deadline filtering, explicit document/monitoring-plan version binding,
a lossless monitoring partition, and history-wide preservation under interleaved
execution, pruning and profile changes. No ADIC implementation,
private checker, numerical certificate format or physical controller is added.

Assumptions not discharged here:
* the chosen policy/context adequately represents applicable requirements;
* observed events, human commands, profile updates and readiness inputs are authentic/complete;
* deployed execution cannot bypass `advance`, and its logical halt is connected
  to an appropriate physical safe-state mechanism;
* clocks/deadlines, durable storage and document identifiers are correctly bound;
* an audit exporter/recoverer satisfies the explicitly supplied round-trip law;
* the chosen monitoring check detects the relevant real-world risks.

In particular, category faithfulness does NOT prove automatic logging, storage
retention, real-world safety or executable replay. The new reference transition
proves recording/stop properties only for its own mathematical model.

Build status is established by the CI run for the exact repository commit.
The existing Lean workflow builds this entire source and checks it with
warnings treated as errors. The optional Python adapter is checked separately;
its presence does not add Python tests to CI. No separate axiom audit is claimed.
-/

universe uE vE uV vV uO vO uF vF

open CategoryTheory

namespace EUAIActMapping

attribute [local instance] ResponsibilityOS.IndexedAssurance.fiberCategory

/-- Opaque deployment/document keys, not hashes or a model of Annex IV contents. -/
structure Context where
  system : Nat
  release : Nat
  specification : Nat
  boundary : Nat
  documentation : Nat
  deriving DecidableEq, Repr

/-- An interpreted technical profile, not a legal-compliance certificate. -/
structure Profile (E : Type uE) [Category.{vE} E] where
  context : Context
  policy : ResponsibilityOS.ObservationPolicy E

inductive Request where
  | allow | withhold | stop
  deriving DecidableEq, Repr

inductive Decision where
  | executed | held | stopped
  deriving DecidableEq, Repr

/-- Stop dominates readiness; a withheld output never executes in this model. -/
def gate (halted ready : Bool) (request : Request) : Decision :=
  match halted, request with
  | true, _ => .stopped
  | false, .stop => .stopped
  | false, .withhold => .held
  | false, .allow => if ready then .executed else .held

def Decision.isStopped : Decision → Bool
  | .stopped => true
  | _ => false

/-- One supplied evidence-bearing event. Times are abstract ordered ticks.
`retainUntil` is supplied under the applicable retention policy; this file does
not equate six calendar months with a fixed number of days. -/
structure Event (E : Type uE) [Category.{vE} E] where
  context : Context
  source : E
  target : E
  trace : source ⟶ target
  createdAt : Nat
  retainUntil : Nat
  validWindow : createdAt ≤ retainUntil

/-- A reference-model record of an attempted operation and its gate outcome. -/
structure Record (E : Type uE) [Category.{vE} E] where
  event : Event E
  profileContext : Context
  request : Request
  ready : Bool
  haltedBefore : Bool
  decision : Decision

structure State (E : Type uE) [Category.{vE} E] where
  profile : Profile E
  halted : Bool
  history : List (Record E)

variable {E : Type uE} [Category.{vE} E]

def capture (s : State E) (e : Event E) (request : Request)
    (ready : Bool) : Record E where
  event := e
  profileContext := s.profile.context
  request := request
  ready := ready
  haltedBefore := s.halted
  decision := gate s.halted (ready && decide (e.context = s.profile.context)) request

/-- The context-guarded reference transition. Every attempted step, including hold/stop,
prepends its computed record. This is not a durable-storage implementation. -/
def advance (s : State E) (e : Event E) (request : Request)
    (ready : Bool) : State E :=
  let r := capture s e request ready
  { profile := s.profile, halted := r.decision.isStopped, history := r :: s.history }

namespace Art11

/-- Documentation contribution: bind evidence to the exact declared context. -/
def matchesContext (p : Profile E) (r : Record E) : Bool :=
  decide (r.event.context = p.context ∧ r.profileContext = p.context)

theorem context_check_is_exact (p : Profile E) (r : Record E) :
    matchesContext p r = true ↔
      r.event.context = p.context ∧ r.profileContext = p.context := by
  simp [matchesContext]

/-- Evidence from a different release/specification/boundary/document key
cannot pass this context check. Adequacy of the keys remains external. -/
theorem stale_context_is_rejected (p : Profile E) (r : Record E)
    (h : r.event.context ≠ p.context) : matchesContext p r = false := by
  simp [matchesContext, h]


/-- Public document metadata only. `context.documentation` identifies its version;
`monitoringPlanVersion` names the plan referenced by that document. Neither field
proves document contents, authenticity, completeness or legal adequacy. -/
structure Documentation where
  context : Context
  monitoringPlanVersion : Nat
  deriving DecidableEq, Repr

/-- A document can support this record only in the current declared context. -/
def supportsRecord (p : Profile E) (d : Documentation) (r : Record E) : Bool :=
  decide (d.context = p.context) && matchesContext p r

theorem document_binding_is_exact (p : Profile E) (d : Documentation) (r : Record E) :
    supportsRecord p d r = true ↔
      d.context = p.context ∧ r.event.context = p.context ∧ r.profileContext = p.context := by
  simp [supportsRecord, matchesContext]

/-- Old/different document versions cannot justify evidence under the current
profile, even when the event itself has the current context. This is a consistency
check, not an assertion that old evidence loses its historical validity. -/
theorem stale_document_is_rejected (p : Profile E) (d : Documentation) (r : Record E)
    (h : d.context.documentation ≠ p.context.documentation) :
    supportsRecord p d r = false := by
  have hContext : d.context ≠ p.context := fun hEq => h (congrArg Context.documentation hEq)
  simp [supportsRecord, hContext]

end Art11

namespace Art12

/-- Automatic recording *in the reference transition*, not inferred from
faithfulness of the mathematical kernel. -/
theorem every_step_is_recorded (s : State E) (e : Event E)
    (request : Request) (ready : Bool) :
    capture s e request ready ∈ (advance s e request ready).history := by
  simp [advance]

theorem previous_records_are_preserved (s : State E) (e : Event E)
    (request : Request) (ready : Bool) (r : Record E)
    (h : r ∈ s.history) : r ∈ (advance s e request ready).history := by
  simp [advance, h]

variable {O : Type uO} [Category.{vO} O]

/-- Canonical connection to the existing kernel; no replacement kernel. -/
def standardEvent (K : ResponsibilityOS.Kernel.{uO, vO, uF, vF} O)
    {X Y : O} (f : X ⟶ Y) (context : Context)
    (createdAt retainUntil : Nat) (h : createdAt ≤ retainUntil) :
    Event (ResponsibilityOS.responsibilityCategory K) where
  context := context
  source := (ResponsibilityOS.standardTrace K).obj X
  target := (ResponsibilityOS.standardTrace K).obj Y
  trace := (ResponsibilityOS.standardTrace K).map f
  createdAt := createdAt
  retainUntil := retainUntil
  validWindow := h

/-- The evidence trace retains the supplied base operation. -/
theorem standard_event_keeps_operation
    (K : ResponsibilityOS.Kernel.{uO, vO, uF, vF} O)
    {X Y : O} (f : X ⟶ Y) (context : Context)
    (createdAt retainUntil : Nat) (h : createdAt ≤ retainUntil) :
    (standardEvent K f context createdAt retainUntil h).trace.base = f := by
  rfl

/-- Standard tracing preserves each distinction required by a supplied policy
on operations. This is not completeness of all evidence within each fiber. -/
theorem standard_trace_preserves_policy
    (K : ResponsibilityOS.Kernel.{uO, vO, uF, vF} O)
    (p : ResponsibilityOS.ObservationPolicy O) :
    ResponsibilityOS.PreservesPolicy (ResponsibilityOS.standardTrace K) p := by
  intro X Y f g hRelevant hEqual
  exact p.sound hRelevant
    ((ResponsibilityOS.standard_trace_is_faithful K).map_injective hEqual)

end Art12

namespace Art14

/-- Readiness is an externally supplied technical result. This theorem does
not identify a Boolean with a lawful or substantively safe decision. -/
theorem execution_requires_permission (halted ready : Bool) (request : Request)
    (h : gate halted ready request = .executed) :
    halted = false ∧ request = .allow ∧ ready = true := by
  cases halted <;> cases ready <;> cases request <;> simp_all [gate]

/-- Execution requires both technical readiness and the current context.
The expected context is stored in the same record for subsequent inspection. -/
theorem execution_requires_current_context (s : State E) (e : Event E)
    (request : Request) (ready : Bool)
    (h : (capture s e request ready).decision = .executed) :
    s.halted = false ∧ request = .allow ∧ ready = true ∧
      e.context = s.profile.context := by
  have hGate := execution_requires_permission s.halted
    (ready && decide (e.context = s.profile.context)) request h
  have hReady : ready = true ∧ e.context = s.profile.context := by
    simpa using hGate.2.2
  exact ⟨hGate.1, hGate.2.1, hReady.1, hReady.2⟩

/-- Logical stop is always effective, independently of readiness. Physical
safe stopping, response times, interfaces and human competence are not modeled. -/
theorem stop_always_halts (s : State E) (e : Event E) (ready : Bool) :
    (advance s e .stop ready).halted = true := by
  cases h : s.halted <;>
    simp [advance, capture, gate, Decision.isStopped, h]

theorem withhold_never_executes (s : State E) (e : Event E) (ready : Bool) :
    (capture s e .withhold ready).decision ≠ .executed := by
  cases h : s.halted <;> simp [capture, gate, h]

/-- No implicit restart exists in the reference transition. -/
theorem stopped_state_remains_stopped (s : State E) (e : Event E)
    (request : Request) (ready : Bool) (h : s.halted = true) :
    (advance s e request ready).halted = true := by
  simp [advance, capture, gate, Decision.isStopped, h]

end Art14

namespace Art19

/-- Retention contribution: a reference filter that cannot delete a record
before its externally determined deadline. A deadline may be extended upstream;
legal minimums, exceptions, control of logs and storage availability are external. -/
def pruneExpired (now : Nat) (history : List (Record E)) : List (Record E) :=
  history.filter (fun r => decide (now ≤ r.event.retainUntil))

theorem no_early_deletion (now : Nat) (history : List (Record E))
    (r : Record E) (hMem : r ∈ history)
    (hDeadline : now ≤ r.event.retainUntil) :
    r ∈ pruneExpired now history := by
  simp [pruneExpired, hMem, hDeadline]

/-- Recording and retention are connected, rather than two independent claims. -/
theorem fresh_record_survives_pruning (s : State E) (e : Event E)
    (request : Request) (ready : Bool) (now : Nat)
    (h : now ≤ e.retainUntil) :
    capture s e request ready ∈
      pruneExpired now (advance s e request ready).history := by
  exact no_early_deletion now _ _
    (Art12.every_step_is_recorded s e request ready) h

end Art19

namespace Art43

variable {V : Type uV} [Category.{vV} V]

/-- Assessment-support contribution: an exporter with a left inverse cannot
collapse policy-relevant evidence distinctions. The round-trip law must be
proved for the actual exporter; it is not assumed for arbitrary real software.
This is neither an executable replay theorem nor an Article 43 procedure. -/
theorem recoverable_export_preserves_policy
    (publish : E ⥤ V) (recover : V ⥤ E)
    (hRoundTrip : publish ⋙ recover = 𝟭 E)
    (p : ResponsibilityOS.ObservationPolicy E) :
    ResponsibilityOS.PreservesPolicy publish p := by
  have hFaithful : publish.Faithful :=
    ResponsibilityOS.IndexedAssurance.faithful_of_section
      recover publish hRoundTrip
  intro X Y f g hRelevant hEqual
  exact p.sound hRelevant (hFaithful.map_injective hEqual)

/-- Exporters need only preserve the selected policy. A left inverse above is
a sufficient construction, not a necessary condition or a legal requirement. -/
theorem policy_relevant_distinction_survives
    (publish : E ⥤ V) (p : ResponsibilityOS.ObservationPolicy E)
    (hPreserve : ResponsibilityOS.PreservesPolicy publish p)
    {X Y : E} {f g : X ⟶ Y} (hRelevant : p.relevant f g) :
    publish.map f ≠ publish.map g := by
  exact hPreserve hRelevant

variable {O : Type uO} [Category.{vO} O]

/-- Reuse of the kernel's structural backward-audit factorization.
Unique categorical factorization must not be called execution replay. -/
theorem backward_audit_factorization
    (K : ResponsibilityOS.Kernel.{uO, vO, uF, vF} O)
    {X Y Z : O} (f : X ⟶ Y) (k : Z ⟶ X)
    (b : K.Fiber Y) (c : K.Fiber Z)
    (h : (⟨Z, c⟩ : ResponsibilityOS.responsibilityCategory K) ⟶ ⟨Y, b⟩)
    (hBase : h.base = k ≫ f) :
    ∃! (δ : (⟨Z, c⟩ : ResponsibilityOS.responsibilityCategory K) ⟶
      ⟨X, (K.pull f).obj b⟩),
      δ.base = k ∧ δ ≫ ResponsibilityOS.IndexedAssurance.cartLift K f b = h := by
  exact ResponsibilityOS.backward_audit_factors_uniquely K f k b c h hBase

end Art43

namespace Art72

/-- A minimal, versioned monitoring plan. The check is supplied, not claimed to
identify all relevant risks. Unknown/insufficient evidence should return false. -/
structure MonitoringPlan (E : Type uE) [Category.{vE} E] where
  context : Context
  version : Nat
  check : Record E → Bool

/-- Positive classification requires a current document, its referenced plan,
a current event/profile binding, and a successful supplied check. A mismatched
plan or document fails closed even if `check` always returns true. -/
def passesPlan (p : Profile E) (d : Art11.Documentation)
    (plan : MonitoringPlan E) (r : Record E) : Bool :=
  decide (plan.context = p.context ∧ plan.version = d.monitoringPlanVersion) &&
    Art11.supportsRecord p d r && plan.check r

def normalRecords (p : Profile E) (d : Art11.Documentation) (plan : MonitoringPlan E)
    (history : List (Record E)) : List (Record E) :=
  history.filter (passesPlan p d plan)

def reviewRecords (p : Profile E) (d : Art11.Documentation) (plan : MonitoringPlan E)
    (history : List (Record E)) : List (Record E) :=
  history.filter (fun r => !(passesPlan p d plan r))

/-- Every supplied recorded item belongs to exactly one classification. `normal`
means this profile's checks passed, not that the real system is safe/compliant. -/
theorem monitoring_complete (p : Profile E) (d : Art11.Documentation)
    (plan : MonitoringPlan E) (history : List (Record E)) (r : Record E)
    (hMem : r ∈ history) :
    (r ∈ normalRecords p d plan history ∨ r ∈ reviewRecords p d plan history) ∧
      ¬ (r ∈ normalRecords p d plan history ∧ r ∈ reviewRecords p d plan history) := by
  cases h : passesPlan p d plan r <;> simp [normalRecords, reviewRecords, hMem, h]

/-- Unlike a membership-only claim, this also accounts for repeated occurrences.
It says nothing about real events absent from the supplied history. -/
theorem monitoring_preserves_occurrences (p : Profile E) (d : Art11.Documentation)
    (plan : MonitoringPlan E) (history : List (Record E)) :
    (normalRecords p d plan history).length + (reviewRecords p d plan history).length =
      history.length := by
  induction history with
  | nil => simp [normalRecords, reviewRecords]
  | cons r history ih =>
      cases h : passesPlan p d plan r <;>
        simpa [normalRecords, reviewRecords, h, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using congrArg Nat.succ ih

theorem failed_plan_check_is_reviewed (p : Profile E) (d : Art11.Documentation)
    (plan : MonitoringPlan E) (history : List (Record E)) (r : Record E)
    (hMem : r ∈ history) (hFail : plan.check r = false) :
    r ∈ reviewRecords p d plan history := by
  simp [reviewRecords, passesPlan, hMem, hFail]

/-- A plan version not referenced by the document cannot clear any item. -/
theorem unmatched_plan_flags_all (p : Profile E) (d : Art11.Documentation)
    (plan : MonitoringPlan E) (history : List (Record E))
    (h : plan.version ≠ d.monitoringPlanVersion) :
    normalRecords p d plan history = [] ∧ reviewRecords p d plan history = history := by
  simp [normalRecords, reviewRecords, passesPlan, h]

/-- Context changes require revalidation, not silent reuse of old documents. -/
theorem outdated_document_flags_all (p : Profile E) (d : Art11.Documentation)
    (plan : MonitoringPlan E) (history : List (Record E)) (h : d.context ≠ p.context) :
    normalRecords p d plan history = [] ∧ reviewRecords p d plan history = history := by
  simp [normalRecords, reviewRecords, passesPlan, Art11.supportsRecord, h]


/-- Monitoring contribution: select every recorded context mismatch or failed
supplied check. No claim that `check` covers all real risks or legal duties. -/
def reviewQueue (p : Profile E) (check : Record E → Bool)
    (history : List (Record E)) : List (Record E) :=
  history.filter (fun r => !(Art11.matchesContext p r && check r))

theorem failed_check_is_flagged (p : Profile E) (check : Record E → Bool)
    (history : List (Record E)) (r : Record E)
    (hMem : r ∈ history) (hFail : check r = false) :
    r ∈ reviewQueue p check history := by
  simp [reviewQueue, hMem, hFail]

theorem changed_context_is_flagged (p : Profile E) (check : Record E → Bool)
    (history : List (Record E)) (r : Record E)
    (hMem : r ∈ history) (hChange : r.event.context ≠ p.context) :
    r ∈ reviewQueue p check history := by
  simp [reviewQueue, Art11.matchesContext, hMem, hChange]

variable {O : Type uO} [Category.{vO} O]

/-- Structural composition support, not a market-monitoring plan. A composite
morphism need not determine its intermediate history; keep the event list too. -/
theorem standard_trace_composes
    (K : ResponsibilityOS.Kernel.{uO, vO, uF, vF} O)
    {X Y Z : O} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (ResponsibilityOS.standardTrace K).map (f ≫ g) =
      (ResponsibilityOS.standardTrace K).map f ≫
        (ResponsibilityOS.standardTrace K).map g := by
  exact (ResponsibilityOS.standardTrace K).map_comp f g

end Art72

/-- One captured record connects document/context binding, logging/retention,
permission, policy-preserving export, and versioned plan-based monitoring.
Document/event context and retention are explicit premises; plan mismatches are
NOT assumed away and cause review. The external export round-trip law remains
an explicit premise. This is not a theorem of legal compliance.

Instantiate E with `ResponsibilityOS.responsibilityCategory K` and use
`Art12.standardEvent`, or supply another justified evidence adapter. -/
theorem evidence_chain
    {V : Type uV} [Category.{vV} V]
    (s : State E) (e : Event E) (d : Art11.Documentation) (plan : Art72.MonitoringPlan E)
    (request : Request) (ready : Bool) (now : Nat)
    (hContext : e.context = s.profile.context) (hDocument : d.context = s.profile.context)
    (hDeadline : now ≤ e.retainUntil)
    (publish : E ⥤ V) (recover : V ⥤ E)
    (hRoundTrip : publish ⋙ recover = 𝟭 E) :
    Art11.supportsRecord s.profile d (capture s e request ready) = true ∧
    capture s e request ready ∈
      Art19.pruneExpired now (advance s e request ready).history ∧
    ((capture s e request ready).decision = .executed →
      s.halted = false ∧ request = .allow ∧ ready = true ∧
        e.context = s.profile.context) ∧
    ResponsibilityOS.PreservesPolicy publish s.profile.policy ∧
    ((capture s e request ready ∈ Art72.normalRecords s.profile d plan
        (Art19.pruneExpired now (advance s e request ready).history) ∨
      capture s e request ready ∈ Art72.reviewRecords s.profile d plan
        (Art19.pruneExpired now (advance s e request ready).history)) ∧
      ¬ (capture s e request ready ∈ Art72.normalRecords s.profile d plan
          (Art19.pruneExpired now (advance s e request ready).history) ∧
        capture s e request ready ∈ Art72.reviewRecords s.profile d plan
          (Art19.pruneExpired now (advance s e request ready).history))) ∧
    (plan.check (capture s e request ready) = false →
      capture s e request ready ∈ Art72.reviewRecords s.profile d plan
        (Art19.pruneExpired now (advance s e request ready).history)) := by
  have hRetained :=
    Art19.fresh_record_survives_pruning s e request ready now hDeadline
  refine ⟨?_, hRetained, ?_, ?_, ?_, ?_⟩
  · simp [Art11.supportsRecord, Art11.matchesContext, capture, hContext, hDocument]
  · intro hExecute
    exact Art14.execution_requires_current_context s e request ready hExecute
  · exact Art43.recoverable_export_preserves_policy publish recover hRoundTrip s.profile.policy
  · exact Art72.monitoring_complete s.profile d plan _ _ hRetained
  · intro hFail
    exact Art72.failed_plan_check_is_reviewed s.profile d plan _ _ hRetained hFail

namespace Examples

/-- A constructive positive witness, with an actually inhabited relevance
relation: the existing kernel's traceA/traceB example, not an empty policy. -/
theorem full_view_preserves_nonempty_trace_policy :
    ResponsibilityOS.PreservesPolicy
      (𝟭 ResponsibilityOS.CollapseCounterexample.EObj)
      ResponsibilityOS.CollapseCounterexample.tracePolicy ∧
    ResponsibilityOS.CollapseCounterexample.tracePolicy.relevant
      ResponsibilityOS.CollapseCounterexample.EHom.traceA
      ResponsibilityOS.CollapseCounterexample.EHom.traceB := by
  constructor
  · intro X Y f g hRelevant hEqual
    exact ResponsibilityOS.CollapseCounterexample.tracePolicy.sound hRelevant hEqual
  · exact ResponsibilityOS.CollapseCounterexample.trace_policy_relevant

/-- Negative witness: an operation-only view does not pass this trace policy. -/
theorem operation_only_view_fails :
    ¬ ResponsibilityOS.PreservesPolicy
      ResponsibilityOS.CollapseCounterexample.U
      ResponsibilityOS.CollapseCounterexample.tracePolicy := by
  exact ResponsibilityOS.CollapseCounterexample.U_does_not_preserve_trace_policy

end Examples

namespace History

/-- Interleave existing operations, retention filtering and profile changes.
A profile change does not erase history or restart a stopped controller. -/
inductive Command (E : Type uE) [Category.{vE} E] where
  | attempt (event : Event E) (request : Request) (ready : Bool)
  | prune (cutoff : Nat)
  | reprofile (profile : Profile E)

def step (s : State E) : Command E → State E
  | .attempt e q b => advance s e q b
  | .prune t => { s with history := Art19.pruneExpired t s.history }
  | .reprofile p => { s with profile := p }

def run (s : State E) : List (Command E) → State E
  | [] => s
  | c :: cs => run (step s c) cs

/-- Reference execution: same operations and profile changes, without deletion. -/
def withoutPruning : List (Command E) → List (Command E)
  | [] => []
  | .prune _ :: cs => withoutPruning cs
  | c :: cs => c :: withoutPruning cs

/-- No deletion is performed using a cutoff later than the final audit time.
This does not assert that a supplied clock is authentic or legally appropriate. -/
def CutoffsWithin (now : Nat) : List (Command E) → Prop
  | [] => True
  | .prune t :: cs => t ≤ now ∧ CutoffsWithin now cs
  | _ :: cs => CutoffsWithin now cs

/-- Retention filters compose without losing an item live at the later cutoff. -/
theorem prune_twice (earlier later : Nat) (hTime : earlier ≤ later)
    (history : List (Record E)) :
    Art19.pruneExpired later (Art19.pruneExpired earlier history) =
      Art19.pruneExpired later history := by
  induction history with
  | nil => rfl
  | cons r _rs ih =>
      by_cases hLater : later ≤ r.event.retainUntil
      · have hEarlier := Nat.le_trans hTime hLater
        simpa [Art19.pruneExpired, hLater, hEarlier] using congrArg (List.cons r) ih
      · by_cases hEarlier : earlier ≤ r.event.retainUntil
        · simpa [Art19.pruneExpired, hLater, hEarlier] using ih
        · simpa [Art19.pruneExpired, hLater, hEarlier] using ih

/-- Relational invariant: equal control states and equal still-retained histories. -/
def SameAt (now : Nat) (s t : State E) : Prop :=
  s.profile = t.profile ∧ s.halted = t.halted ∧
    Art19.pruneExpired now s.history = Art19.pruneExpired now t.history

private theorem advance_sameAt (now : Nat) (s t : State E)
    (h : SameAt now s t) (e : Event E) (q : Request) (b : Bool) :
    SameAt now (advance s e q b) (advance t e q b) := by
  have hCapture : capture s e q b = capture t e q b := by
    simp only [capture, h.1, h.2.1]
  refine ⟨h.1, ?_, ?_⟩
  · change (capture s e q b).decision.isStopped = (capture t e q b).decision.isStopped
    rw [hCapture]
  · change Art19.pruneExpired now (capture s e q b :: s.history) =
      Art19.pruneExpired now (capture t e q b :: t.history)
    have hHistory := h.2.2
    dsimp only [Art19.pruneExpired] at hHistory
    simp only [Art19.pruneExpired, List.filter_cons]
    rw [hCapture, hHistory]

/-- Induction over arbitrary interleavings, not a single-record conjunction.
Dropping intermediate pruning preserves control state and the exact final live
list, including order and repeated occurrences, when all cutoffs are in range. -/
theorem run_without_pruning (now : Nat) (commands : List (Command E)) :
    ∀ s t : State E, CutoffsWithin now commands → SameAt now s t →
      SameAt now (run s commands) (run t (withoutPruning commands)) := by
  induction commands with
  | nil => intro s t _ h; exact h
  | cons c _cs ih =>
      intro s t hTime h
      cases c with
      | attempt e q b =>
          exact ih (advance s e q b) (advance t e q b) hTime
            (advance_sameAt now s t h e q b)
      | prune cutoff =>
          apply ih (step s (.prune cutoff)) t hTime.2
          exact ⟨h.1, h.2.1, (prune_twice cutoff now hTime.1 s.history).trans h.2.2⟩
      | reprofile p =>
          exact ih (step s (.reprofile p)) (step t (.reprofile p)) hTime
            ⟨rfl, h.2.1, h.2.2⟩

/-- Permission is checked against the context captured at execution, not a later
profile. Reconfiguration must not rewrite the meaning of historical records. -/
def Permission (r : Record E) : Prop :=
  r.decision = .executed →
    r.haltedBefore = false ∧ r.request = .allow ∧ r.ready = true ∧
      r.event.context = r.profileContext

private theorem step_permission (s : State E) (c : Command E)
    (h : ∀ r ∈ s.history, Permission r) :
    ∀ r ∈ (step s c).history, Permission r := by
  cases c with
  | attempt e q b =>
      intro r hMem
      change r ∈ capture s e q b :: s.history at hMem
      rcases List.mem_cons.mp hMem with hEq | hOld
      · subst r
        exact Art14.execution_requires_current_context s e q b
      · exact h r hOld
  | prune _ =>
      intro r hMem
      exact h r (List.mem_filter.mp hMem).1
  | reprofile _ => exact h

theorem run_permission (commands : List (Command E)) :
    ∀ s : State E, (∀ r ∈ s.history, Permission r) →
      ∀ r ∈ (run s commands).history, Permission r := by
  induction commands with
  | nil => intro s h; exact h
  | cons c _cs ih => intro s h; exact ih (step s c) (step_permission s c h)

/-- No sequence of pruning, profile changes or attempted operations silently
restarts a stopped reference controller. -/
theorem stopped_run_stays_stopped (commands : List (Command E)) :
    ∀ s : State E, s.halted = true → (run s commands).halted = true := by
  induction commands with
  | nil => intro s h; exact h
  | cons c _cs ih =>
      intro s h
      apply ih (step s c)
      cases c with
      | attempt e q b => exact Art14.stopped_state_remains_stopped s e q b h
      | prune _ => exact h
      | reprofile _ => exact h

/-- Positive case: an allowed, ready operation in the matching context really
executes, and a subsequent permitted retention filter keeps its record. -/
theorem live_execution_survives_pruning (s : State E) (e : Event E) (now : Nat)
    (hHalted : s.halted = false) (hContext : e.context = s.profile.context)
    (hDeadline : now ≤ e.retainUntil) :
    (run s [.attempt e .allow true, .prune now]).history =
        capture s e .allow true :: Art19.pruneExpired now s.history ∧
      (capture s e .allow true).decision = .executed := by
  constructor
  · simp [run, step, advance, Art19.pruneExpired, capture, hDeadline]
  · simp [capture, gate, hHalted, hContext]

/-- A future-dated deletion really breaks a retrospective live-record claim.
The cutoff premise above is necessary; it is not a decorative assumption. -/
theorem future_cutoff_counterexample (r : Record E) :
    Art19.pruneExpired r.event.retainUntil
        (Art19.pruneExpired (r.event.retainUntil + 1) [r]) = [] ∧
      Art19.pruneExpired r.event.retainUntil [r] = [r] := by
  simp [Art19.pruneExpired]

end History

/-- History-wide chain for an initially empty reference history. Permission is
DERIVED from execution, not assumed for every output record. All prune cutoffs
must be no later than `now`. The final document/plan need not match: an unmatched
record is sent to review, not silently treated as current supporting evidence.
The export round-trip is an explicit sufficient condition, not an Act requirement.
Neither actual data capture nor physical execution nor legal adequacy is proved. -/
theorem history_evidence_chain
    {V : Type uV} [Category.{vV} V]
    (s : State E) (hEmpty : s.history = [])
    (commands : List (History.Command E)) (now : Nat)
    (hTime : History.CutoffsWithin now commands)
    (d : Art11.Documentation) (plan : Art72.MonitoringPlan E)
    (publish : E ⥤ V) (recover : V ⥤ E)
    (hRoundTrip : publish ⋙ recover = 𝟭 E) :
    let after := History.run s commands
    let reference := History.run s (History.withoutPruning commands)
    let kept := Art19.pruneExpired now after.history
    kept = Art19.pruneExpired now reference.history ∧
    (∀ r ∈ reference.history, now ≤ r.event.retainUntil →
      r ∈ kept ∧ History.Permission r ∧
      ((r ∈ Art72.normalRecords after.profile d plan kept ∨
        r ∈ Art72.reviewRecords after.profile d plan kept) ∧
        ¬ (r ∈ Art72.normalRecords after.profile d plan kept ∧
          r ∈ Art72.reviewRecords after.profile d plan kept)) ∧
      (r ∈ Art72.normalRecords after.profile d plan kept →
        Art11.supportsRecord after.profile d r = true) ∧
      (Art72.passesPlan after.profile d plan r = false →
        r ∈ Art72.reviewRecords after.profile d plan kept) ∧
      (∀ g : r.event.source ⟶ r.event.target,
        after.profile.policy.relevant r.event.trace g →
          publish.map r.event.trace ≠ publish.map g)) ∧
    (Art72.normalRecords after.profile d plan kept).length +
      (Art72.reviewRecords after.profile d plan kept).length = kept.length := by
  dsimp only
  have hSame := History.run_without_pruning now commands s s hTime ⟨rfl, rfl, rfl⟩
  have hInitial : ∀ r ∈ s.history, History.Permission r := by simp [hEmpty]
  have hPermission := History.run_permission commands s hInitial
  have hExport :
      ResponsibilityOS.PreservesPolicy publish (History.run s commands).profile.policy :=
    Art43.recoverable_export_preserves_policy publish recover hRoundTrip
      (History.run s commands).profile.policy
  refine ⟨hSame.2.2, ?_, Art72.monitoring_preserves_occurrences _ d plan _⟩
  intro r hReference hLive
  have hKept : r ∈ Art19.pruneExpired now (History.run s commands).history := by
    rw [hSame.2.2]
    exact Art19.no_early_deletion now _ r hReference hLive
  refine ⟨hKept, hPermission r (List.mem_filter.mp hKept).1,
    Art72.monitoring_complete _ d plan _ r hKept, ?_, ?_, ?_⟩
  · intro hNormal
    have hPass : Art72.passesPlan (History.run s commands).profile d plan r = true :=
      (List.mem_filter.mp hNormal).2
    cases hSupport : Art11.supportsRecord (History.run s commands).profile d r with
    | false =>
        simp [Art72.passesPlan, hSupport] at hPass
    | true =>
        rfl
  · intro hFail
    simp [Art72.reviewRecords, hKept, hFail]
  · intro g hRelevant
    exact hExport hRelevant


/-!
# Hiroshima AI Process -> Responsibility OS -> selected EU technical profiles

Copyright (c) 2026 AI Assurance, Inc. All rights reserved. See README.md.

This is an additive, independently scoped application namespace. The official
HAIP Code of Conduct (MOFA, 2023-10-30, https://www.mofa.go.jp/files/100573473.pdf)
is the normative starting point, not a private HAIP mapping or a cold-chain
profile. The interpretation table in README.md is external to these proofs.

Evidence status, evidence role, intended use, actor role, system/version context,
missing obligations and nonempty evidence identifiers are distinct. A source
profile does not certify a target profile. A checked route reuses only named
shared technical obligations, and separately checks target additions.
- No legal implication HAIP-compliant -> EU-compliant is asserted.
- No authenticity, complete risk identification or physical safety is inferred
  from a status flag, a hash, a source label or the existence of this proof.
- The example vocabulary is open (natural-number requirement identifiers), not
  a restriction of Responsibility OS to these checks or to this industry.
-/

namespace CrossFramework

inductive EvidenceStage where
  | model | implementation | operation
  deriving DecidableEq, Repr

inductive Status where
  | supported | failed | unknown | notCovered | notAssessed | notApplicable
  deriving DecidableEq, Repr

/-- `code` names an explicitly interpreted technical obligation, not an article.
`stage` prevents a model proof from silently becoming run-specific evidence. -/
structure Requirement where
  code : Nat
  stage : EvidenceStage
  deriving DecidableEq, Repr

/-- A context must include the intended use and actor role as well as the five
existing version/boundary keys. IDs are external bindings, not authentication. -/
structure Scope where
  context : Context
  purpose : Nat
  actorRole : Nat
  deriving DecidableEq, Repr

/-- A supplied assessment entry. Evidence IDs must reference inspected artifacts;
their mere presence is not a proof that those artifacts establish the claim. -/
structure Entry where
  requirement : Requirement
  scope : Scope
  observedStage : EvidenceStage
  status : Status
  evidenceIds : List Nat
  gapIds : List Nat
  deriving DecidableEq, Repr

def entrySupports (scope : Scope) (q : Requirement) (e : Entry) : Bool :=
  decide (e.requirement = q ∧ e.scope = scope ∧ e.observedStage = q.stage ∧
    e.status = .supported) &&
    decide (e.evidenceIds ≠ []) && e.evidenceIds.all (fun n => decide (n ≠ 0)) &&
    decide (e.gapIds = [])

def supports (scope : Scope) (entries : List Entry) (q : Requirement) : Bool :=
  entries.any (entrySupports scope q)

/-- Ambiguous duplicate requirement entries invalidate a transfer, rather than
letting a favourable duplicate override an adverse finding. Raw entries remain. -/
def uniqueEntries (entries : List Entry) : Bool :=
  decide ((entries.map Entry.requirement).Nodup)

def allSupported (scope : Scope) (entries : List Entry) : List Requirement → Bool
  | [] => true
  | q :: qs => supports scope entries q && allSupported scope entries qs

def missing (scope : Scope) (entries : List Entry) (qs : List Requirement) :
    List Requirement := qs.filter (fun q => !(supports scope entries q))

theorem allSupported_iff (scope : Scope) (entries : List Entry)
    (qs : List Requirement) :
    allSupported scope entries qs = true ↔
      ∀ q ∈ qs, supports scope entries q = true := by
  induction qs with
  | nil => simp [allSupported]
  | cons q qs ih => simp [allSupported, ih]

theorem allSupported_append (scope : Scope) (entries : List Entry)
    (xs ys : List Requirement) :
    allSupported scope entries (xs ++ ys) =
      (allSupported scope entries xs && allSupported scope entries ys) := by
  induction xs with
  | nil => simp [allSupported]
  | cons q qs ih => simp [allSupported, ih, Bool.and_assoc]

theorem missing_is_exact (scope : Scope) (entries : List Entry)
    (qs : List Requirement) (q : Requirement) :
    q ∈ missing scope entries qs ↔
      q ∈ qs ∧ supports scope entries q = false := by
  simp [missing]

theorem unsupported_status_rejected (scope : Scope) (q : Requirement) (e : Entry)
    (h : e.status ≠ .supported) : entrySupports scope q e = false := by
  simp [entrySupports, h]

theorem wrong_evidence_stage_rejected (scope : Scope) (q : Requirement) (e : Entry)
    (h : e.observedStage ≠ q.stage) : entrySupports scope q e = false := by
  simp [entrySupports, h]

theorem evidence_without_artifacts_rejected (scope : Scope) (q : Requirement)
    (e : Entry) (h : e.evidenceIds = []) : entrySupports scope q e = false := by
  simp [entrySupports, h]

theorem material_gap_rejected (scope : Scope) (q : Requirement) (e : Entry)
    (h : e.gapIds ≠ []) : entrySupports scope q e = false := by
  simp [entrySupports, h]

/-- The route is a published interpretation, not user-controlled permission.
`shared` names the exact obligations reused; `additional` is checked independently.
Additional means additional to this source profile, not exclusive to EU law. -/
structure Route where
  source : List Requirement
  shared : List Requirement
  additional : List Requirement
  deriving DecidableEq, Repr

def linked (route : Route) : Bool :=
  route.shared.all (fun q => decide (q ∈ route.source))

def targetRequirements (route : Route) : List Requirement :=
  route.shared ++ route.additional

def ready (route : Route) (sourceScope targetScope : Scope)
    (entries : List Entry) : Bool :=
  decide (route.shared ≠ []) && linked route && decide (sourceScope = targetScope) &&
    uniqueEntries entries && allSupported sourceScope entries route.source &&
    allSupported targetScope entries route.additional

theorem ready_parts (route : Route) (sourceScope targetScope : Scope)
    (entries : List Entry) :
    ready route sourceScope targetScope entries = true ↔
      route.shared ≠ [] ∧ linked route = true ∧ sourceScope = targetScope ∧
        uniqueEntries entries = true ∧
        allSupported sourceScope entries route.source = true ∧
        allSupported targetScope entries route.additional = true := by
  simp [ready, and_assoc]

/-- The shared conclusion is derived from source evidence and an explicit
inclusion, not assumed as a target certificate. -/
theorem source_guarantee_inherited (route : Route) (scope : Scope)
    (entries : List Entry) (hLink : linked route = true)
    (hSource : allSupported scope entries route.source = true) :
    allSupported scope entries route.shared = true := by
  have hInclusion : ∀ q ∈ route.shared, q ∈ route.source := by
    simpa [linked] using hLink
  apply (allSupported_iff scope entries route.shared).mpr
  intro q hMem
  exact (allSupported_iff scope entries route.source).mp hSource q (hInclusion q hMem)

/-- Main transfer theorem. Source validation covers only the mapped shared
obligations. Both the target additions and the full use/role/context match are
necessary. This is a technical-profile theorem, not a legal equivalence. -/
theorem target_evidence_is_derived (route : Route) (sourceScope targetScope : Scope)
    (entries : List Entry) (h : ready route sourceScope targetScope entries = true) :
    allSupported targetScope entries (targetRequirements route) = true := by
  rcases (ready_parts route sourceScope targetScope entries).mp h with
    ⟨_, hLink, hScope, _, hSource, hExtra⟩
  have hShared : allSupported targetScope entries route.shared = true := by
    simpa [hScope] using source_guarantee_inherited route sourceScope entries hLink hSource
  simp [targetRequirements, allSupported_append, hShared, hExtra]

/-- A missing *shared or additional* target obligation blocks transfer. -/
theorem missing_target_blocks_transfer (route : Route) (sourceScope targetScope : Scope)
    (entries : List Entry) (q : Requirement)
    (hMem : q ∈ targetRequirements route)
    (hFail : supports targetScope entries q = false) :
    ready route sourceScope targetScope entries ≠ true := by
  intro hReady
  have hPass := (allSupported_iff targetScope entries (targetRequirements route)).mp
    (target_evidence_is_derived route sourceScope targetScope entries hReady) q hMem
  simp [hFail] at hPass

theorem scope_change_blocks_transfer (route : Route) (sourceScope targetScope : Scope)
    (entries : List Entry) (h : sourceScope ≠ targetScope) :
    ready route sourceScope targetScope entries = false := by
  simp [ready, h]

theorem empty_bridge_is_not_coverage (route : Route) (sourceScope targetScope : Scope)
    (entries : List Entry) (h : route.shared = []) :
    ready route sourceScope targetScope entries = false := by
  simp [ready, h]

theorem duplicate_entries_block_transfer (route : Route) (sourceScope targetScope : Scope)
    (entries : List Entry) (h : uniqueEntries entries = false) :
    ready route sourceScope targetScope entries = false := by
  simp [ready, h]

/-- Adding target obligations cannot enable a transfer that was previously
blocked. Source-profile coverage is never added up to fill target gaps. -/
theorem additional_requirements_cannot_enable (route : Route)
    (sourceScope targetScope : Scope) (entries : List Entry) (more : List Requirement)
    (h : ready { route with additional := route.additional ++ more }
      sourceScope targetScope entries = true) :
    ready route sourceScope targetScope entries = true := by
  rcases (ready_parts _ sourceScope targetScope entries).mp h with
    ⟨hNonempty, hLink, hScope, hUnique, hSource, hExtra⟩
  have hBoth : allSupported targetScope entries route.additional = true ∧
      allSupported targetScope entries more = true := by
    simpa [allSupported_append] using hExtra
  exact (ready_parts route sourceScope targetScope entries).mpr
    ⟨hNonempty, hLink, hScope, hUnique, hSource, hBoth.1⟩

/-- Whole original evidence is retained, including out-of-profile findings.
Missing lists are *views*; they never replace the raw, scoped assessment entries. -/
structure Bundle where
  route : Route
  sourceScope : Scope
  targetScope : Scope
  entries : List Entry
  deriving DecidableEq, Repr

/-- A pure finite interface for Python/Lean concrete-run correspondence checks.
The current profile context is an independent trusted input, not inferred from
the candidate's own scope. The existing `gate` is reused unchanged. -/
def runGate (current eventContext : Context) (halted domainReady : Bool)
    (request : Request) (bundle : Bundle) : Decision :=
  gate halted
    ((domainReady && ready bundle.route bundle.sourceScope bundle.targetScope bundle.entries &&
      decide (bundle.targetScope.context = current)) && decide (eventContext = current)) request

/-- Add evidence-derived readiness to the original capture; do not replace the
Kernel, controller, recording or retention semantics. -/
def captureWithEvidence (s : State E) (e : Event E) (request : Request)
    (domainReady : Bool) (bundle : Bundle) : Record E :=
  capture s e request
    (domainReady && ready bundle.route bundle.sourceScope bundle.targetScope bundle.entries &&
      decide (bundle.targetScope.context = s.profile.context))

theorem runGate_is_capture (s : State E) (e : Event E) (request : Request)
    (domainReady : Bool) (bundle : Bundle) :
    (captureWithEvidence s e request domainReady bundle).decision =
      runGate s.profile.context e.context s.halted domainReady request bundle := by
  rfl

/-- The bridge guard is derived from the actual gate outcome. Its acceptance
premises are not assumed on behalf of every recorded operation. -/
theorem executed_requires_bridge (current eventContext : Context)
    (halted domainReady : Bool) (request : Request) (bundle : Bundle)
    (h : runGate current eventContext halted domainReady request bundle = .executed) :
    halted = false ∧ request = .allow ∧ domainReady = true ∧
      ready bundle.route bundle.sourceScope bundle.targetScope bundle.entries = true ∧
      bundle.targetScope.context = current ∧ eventContext = current := by
  have hGate := Art14.execution_requires_permission halted _ request h
  have hReady : domainReady = true ∧
      ready bundle.route bundle.sourceScope bundle.targetScope bundle.entries = true ∧
      bundle.targetScope.context = current ∧ eventContext = current := by
    simpa [and_assoc] using hGate.2.2
  exact ⟨hGate.1, hGate.2.1, hReady⟩

theorem executed_requires_target_evidence (s : State E) (e : Event E)
    (request : Request) (domainReady : Bool) (bundle : Bundle)
    (h : (captureWithEvidence s e request domainReady bundle).decision = .executed) :
    allSupported bundle.targetScope bundle.entries (targetRequirements bundle.route) = true := by
  have hBridge := executed_requires_bridge s.profile.context e.context s.halted
    domainReady request bundle h
  exact target_evidence_is_derived bundle.route bundle.sourceScope bundle.targetScope
    bundle.entries hBridge.2.2.2.1

theorem missing_target_never_executes (current eventContext : Context)
    (halted domainReady : Bool) (request : Request) (bundle : Bundle) (q : Requirement)
    (hMem : q ∈ targetRequirements bundle.route)
    (hFail : supports bundle.targetScope bundle.entries q = false) :
    runGate current eventContext halted domainReady request bundle ≠ .executed := by
  intro hExecute
  have hBridge := executed_requires_bridge current eventContext halted domainReady request bundle hExecute
  exact missing_target_blocks_transfer bundle.route bundle.sourceScope bundle.targetScope
    bundle.entries q hMem hFail hBridge.2.2.2.1

def advanceWithEvidence (s : State E) (e : Event E) (request : Request)
    (domainReady : Bool) (bundle : Bundle) : State E :=
  advance s e request
    (domainReady && ready bundle.route bundle.sourceScope bundle.targetScope bundle.entries &&
      decide (bundle.targetScope.context = s.profile.context))

/-- Existing Art.12/19 preservation applies to the evidence-gated operation,
including its HOLD or STOP result. -/
theorem evidence_gated_record_is_retained (s : State E) (e : Event E)
    (request : Request) (domainReady : Bool) (bundle : Bundle) (now : Nat)
    (hDeadline : now ≤ e.retainUntil) :
    captureWithEvidence s e request domainReady bundle ∈
      Art19.pruneExpired now (advanceWithEvidence s e request domainReady bundle).history := by
  exact Art19.fresh_record_survives_pruning s e request _ now hDeadline

theorem evidence_gate_cannot_restart (s : State E) (e : Event E)
    (request : Request) (domainReady : Bool) (bundle : Bundle) (h : s.halted = true) :
    (advanceWithEvidence s e request domainReady bundle).halted = true := by
  exact Art14.stopped_state_remains_stopped s e request _ h

structure Receipt (E : Type uE) [Category.{vE} E] where
  original : Bundle
  record : Record E
  sourceMissing : List Requirement
  targetMissing : List Requirement

def receipt (s : State E) (e : Event E) (request : Request)
    (domainReady : Bool) (bundle : Bundle) : Receipt E where
  original := bundle
  record := captureWithEvidence s e request domainReady bundle
  sourceMissing := missing bundle.sourceScope bundle.entries bundle.route.source
  targetMissing := missing bundle.targetScope bundle.entries (targetRequirements bundle.route)

theorem receipt_preserves_all_entries (s : State E) (e : Event E) (request : Request)
    (domainReady : Bool) (bundle : Bundle) :
    (receipt s e request domainReady bundle).original = bundle := by
  rfl

theorem receipt_retains_target_gaps (s : State E) (e : Event E) (request : Request)
    (domainReady : Bool) (bundle : Bundle) (q : Requirement) :
    q ∈ (receipt s e request domainReady bundle).targetMissing ↔
      q ∈ targetRequirements bundle.route ∧ supports bundle.targetScope bundle.entries q = false := by
  exact missing_is_exact bundle.targetScope bundle.entries (targetRequirements bundle.route) q


namespace Audit

/-- The old operational state plus a scoped assessment receipt for each record.
The old state is not changed in place or replaced with a new Kernel. -/
structure State (E : Type uE) [Category.{vE} E] where
  base : EUAIActMapping.State E
  receipts : List (Receipt E)

inductive Command (E : Type uE) [Category.{vE} E] where
  | attempt (event : Event E) (request : Request) (domainReady : Bool) (bundle : Bundle)
  | prune (cutoff : Nat)
  | reprofile (profile : Profile E)

def retain (now : Nat) (receipts : List (Receipt E)) : List (Receipt E) :=
  receipts.filter (fun r => decide (now ≤ r.record.event.retainUntil))

def step (s : State E) : Command E → State E
  | .attempt e q b bundle =>
      { base := advanceWithEvidence s.base e q b bundle
        receipts := receipt s.base e q b bundle :: s.receipts }
  | .prune t =>
      { base := { s.base with history := Art19.pruneExpired t s.base.history }
        receipts := retain t s.receipts }
  | .reprofile p => { s with base := { s.base with profile := p } }

def run (s : State E) : List (Command E) → State E
  | [] => s
  | c :: cs => run (step s c) cs

def withoutPruning : List (Command E) → List (Command E)
  | [] => []
  | .prune _ :: cs => withoutPruning cs
  | c :: cs => c :: withoutPruning cs

def CutoffsWithin (now : Nat) : List (Command E) → Prop
  | [] => True
  | .prune t :: cs => t ≤ now ∧ CutoffsWithin now cs
  | _ :: cs => CutoffsWithin now cs

/-- Validity is evaluated in the captured historical scope. A later profile
change never rewrites the role, intended use or meaning of an old result. -/
def Valid (r : Receipt E) : Prop :=
  r.sourceMissing = missing r.original.sourceScope r.original.entries r.original.route.source ∧
  r.targetMissing = missing r.original.targetScope r.original.entries
    (targetRequirements r.original.route) ∧
  (r.record.decision = .executed →
    r.original.sourceScope = r.original.targetScope ∧
    r.original.targetScope.context = r.record.profileContext ∧
    allSupported r.original.targetScope r.original.entries
      (targetRequirements r.original.route) = true)

theorem issued_receipt_is_valid (s : EUAIActMapping.State E) (e : Event E)
    (q : Request) (b : Bool) (bundle : Bundle) :
    Valid (receipt s e q b bundle) := by
  refine ⟨rfl, rfl, ?_⟩
  intro hExecute
  have hGate := executed_requires_bridge s.profile.context e.context s.halted b q bundle hExecute
  have hReady := hGate.2.2.2.1
  have hScope := ((ready_parts _ _ _ _).mp hReady).2.2.1
  exact ⟨hScope, hGate.2.2.2.2.1,
    target_evidence_is_derived bundle.route bundle.sourceScope bundle.targetScope bundle.entries hReady⟩

private theorem step_valid (s : State E) (c : Command E)
    (h : ∀ r ∈ s.receipts, Valid r) :
    ∀ r ∈ (step s c).receipts, Valid r := by
  cases c with
  | attempt e q b bundle =>
      intro r hMem
      change r ∈ receipt s.base e q b bundle :: s.receipts at hMem
      rcases List.mem_cons.mp hMem with hEq | hOld
      · subst r
        exact issued_receipt_is_valid s.base e q b bundle
      · exact h r hOld
  | prune _ =>
      intro r hMem
      exact h r (List.mem_filter.mp hMem).1
  | reprofile _ => exact h

theorem run_valid (commands : List (Command E)) :
    ∀ s : State E, (∀ r ∈ s.receipts, Valid r) →
      ∀ r ∈ (run s commands).receipts, Valid r := by
  induction commands with
  | nil => intro s h; exact h
  | cons c _cs ih => intro s h; exact ih (step s c) (step_valid s c h)

theorem retain_twice (earlier later : Nat) (hTime : earlier ≤ later)
    (receipts : List (Receipt E)) :
    retain later (retain earlier receipts) = retain later receipts := by
  induction receipts with
  | nil => rfl
  | cons r _rs ih =>
      by_cases hLater : later ≤ r.record.event.retainUntil
      · have hEarlier := Nat.le_trans hTime hLater
        simpa [retain, hLater, hEarlier] using congrArg (List.cons r) ih
      · by_cases hEarlier : earlier ≤ r.record.event.retainUntil
        · simpa [retain, hLater, hEarlier] using ih
        · simpa [retain, hLater, hEarlier] using ih

def SameAt (now : Nat) (s t : State E) : Prop :=
  s.base.profile = t.base.profile ∧ s.base.halted = t.base.halted ∧
    retain now s.receipts = retain now t.receipts

private theorem attempt_sameAt (now : Nat) (s t : State E) (h : SameAt now s t)
    (e : Event E) (q : Request) (b : Bool) (bundle : Bundle) :
    SameAt now (step s (.attempt e q b bundle)) (step t (.attempt e q b bundle)) := by
  have hReceipt : receipt s.base e q b bundle = receipt t.base e q b bundle := by
    simp only [receipt, captureWithEvidence, capture, h.1, h.2.1]
  have hRecord : captureWithEvidence s.base e q b bundle =
      captureWithEvidence t.base e q b bundle := congrArg Receipt.record hReceipt
  refine ⟨h.1, ?_, ?_⟩
  · change (captureWithEvidence s.base e q b bundle).decision.isStopped =
      (captureWithEvidence t.base e q b bundle).decision.isStopped
    rw [hRecord]
  · change retain now (receipt s.base e q b bundle :: s.receipts) =
      retain now (receipt t.base e q b bundle :: t.receipts)
    have hHistory := h.2.2
    dsimp only [retain] at hHistory
    simp only [retain, List.filter_cons]
    rw [hReceipt, hHistory]

/-- Exact list equality for *whole receipts*, not merely their verdicts or counts.
It preserves original evidence, unassessed findings, role/use/version scope,
missing lists, ordering and repeated occurrences through arbitrary interleavings.
As with the original History theorem, no pruning cutoff may exceed the final
inspection cutoff. Controllers depending on deleted history need a new proof. -/
theorem run_without_pruning (now : Nat) (commands : List (Command E)) :
    ∀ s t : State E, CutoffsWithin now commands → SameAt now s t →
      SameAt now (run s commands) (run t (withoutPruning commands)) := by
  induction commands with
  | nil => intro s t _ h; exact h
  | cons c _cs ih =>
      intro s t hTime h
      cases c with
      | attempt e q b bundle =>
          exact ih (step s (.attempt e q b bundle)) (step t (.attempt e q b bundle))
            hTime (attempt_sameAt now s t h e q b bundle)
      | prune cutoff =>
          apply ih (step s (.prune cutoff)) t hTime.2
          exact ⟨h.1, h.2.1, (retain_twice cutoff now hTime.1 s.receipts).trans h.2.2⟩
      | reprofile p =>
          exact ih (step s (.reprofile p)) (step t (.reprofile p)) hTime
            ⟨rfl, h.2.1, h.2.2⟩


/-- The richer receipt list and the original operational record list refer to
exactly the same occurrences. Both empty lists satisfy this initial invariant. -/
def Synchronized (s : State E) : Prop :=
  s.receipts.map Receipt.record = s.base.history

private theorem retained_records (now : Nat) (receipts : List (Receipt E)) :
    (retain now receipts).map Receipt.record =
      Art19.pruneExpired now (receipts.map Receipt.record) := by
  induction receipts with
  | nil => rfl
  | cons r _rs ih =>
      by_cases hLive : now ≤ r.record.event.retainUntil
      · simpa [retain, Art19.pruneExpired, hLive] using congrArg (List.cons r.record) ih
      · simpa [retain, Art19.pruneExpired, hLive] using ih

private theorem step_synchronized (s : State E) (c : Command E)
    (h : Synchronized s) : Synchronized (step s c) := by
  change s.receipts.map Receipt.record = s.base.history at h
  cases c with
  | attempt e q b bundle =>
      change (receipt s.base e q b bundle :: s.receipts).map Receipt.record =
        captureWithEvidence s.base e q b bundle :: s.base.history
      change captureWithEvidence s.base e q b bundle :: s.receipts.map Receipt.record =
        captureWithEvidence s.base e q b bundle :: s.base.history
      rw [h]
  | prune cutoff =>
      change (retain cutoff s.receipts).map Receipt.record =
        Art19.pruneExpired cutoff s.base.history
      rw [retained_records, h]
  | reprofile _ => exact h

theorem run_synchronized (commands : List (Command E)) :
    ∀ s : State E, Synchronized s → Synchronized (run s commands) := by
  induction commands with
  | nil => intro s h; exact h
  | cons c _cs ih => intro s h; exact ih (step s c) (step_synchronized s c h)

/-- The integrated cross-framework history result starts from justified initial
receipts (in particular an empty receipt list). Live source/target evidence and
gaps match a no-deletion run, and each executed receipt has the target evidence
under its own captured scope. Neither conclusion is supplied as a final premise. -/
theorem history_transfer_and_preservation (s : State E)
    (hInitial : ∀ r ∈ s.receipts, Valid r) (commands : List (Command E)) (now : Nat)
    (hTime : CutoffsWithin now commands) :
    retain now (run s commands).receipts =
      retain now (run s (withoutPruning commands)).receipts ∧
    ∀ r ∈ retain now (run s commands).receipts, Valid r := by
  have hSame := run_without_pruning now commands s s hTime ⟨rfl, rfl, rfl⟩
  refine ⟨hSame.2.2, ?_⟩
  intro r hMem
  exact run_valid commands s hInitial r (List.mem_filter.mp hMem).1

end Audit

/-- Independent source/target observation policies; neither silently replaces
the other when evidence is exported across frameworks. -/
def jointPolicy (source target : ResponsibilityOS.ObservationPolicy E) :
    ResponsibilityOS.ObservationPolicy E where
  relevant := fun f g => source.relevant f g ∨ target.relevant f g
  sound := by
    intro X Y f g h
    rcases h with hSource | hTarget
    · exact source.sound hSource
    · exact target.sound hTarget

theorem joint_policy_preservation_iff {V : Type uV} [Category.{vV} V]
    (publish : E ⥤ V) (source target : ResponsibilityOS.ObservationPolicy E) :
    ResponsibilityOS.PreservesPolicy publish (jointPolicy source target) ↔
      ResponsibilityOS.PreservesPolicy publish source ∧
        ResponsibilityOS.PreservesPolicy publish target := by
  constructor
  · intro h
    constructor
    · intro X Y f g hSource
      exact h (Or.inl hSource)
    · intro X Y f g hTarget
      exact h (Or.inr hTarget)
  · rintro ⟨hSource, hTarget⟩ X Y f g h
    rcases h with hS | hT
    · exact hSource hS
    · exact hTarget hT

theorem recoverable_export_preserves_both {V : Type uV} [Category.{vV} V]
    (publish : E ⥤ V) (recover : V ⥤ E) (hRoundTrip : publish ⋙ recover = 𝟭 E)
    (source target : ResponsibilityOS.ObservationPolicy E) :
    ResponsibilityOS.PreservesPolicy publish source ∧
      ResponsibilityOS.PreservesPolicy publish target := by
  exact (joint_policy_preservation_iff publish source target).mp
    (Art43.recoverable_export_preserves_policy publish recover hRoundTrip (jointPolicy source target))

namespace Hiroshima

/-- Official Code of Conduct action identifiers (2023-10-30 baseline).
Enumerating an action does not claim that the action is fully implemented. -/
inductive Action where
  | a1 | a2 | a3 | a4 | a5 | a6 | a7 | a8 | a9 | a10 | a11
  deriving DecidableEq, Repr

/-- Open example vocabulary: only selected, operation-level technical checks. -/
def riskTest : Requirement := ⟨1, .operation⟩
def inputEvidence : Requirement := ⟨2, .operation⟩
def traceBinding : Requirement := ⟨3, .operation⟩
def currentDocument : Requirement := ⟨4, .operation⟩
def currentPlan : Requirement := ⟨5, .operation⟩

/-- Author interpretation reviewed against the official HAIP text; not a theorem
that a check implements a whole action. Other codes remain available. -/
def relatedActions (q : Requirement) : List Action :=
  match q.code with
  | 1 => [.a1, .a5]
  | 2 => [.a1, .a5]
  | 3 => [.a3, .a4, .a10]
  | 4 => [.a1, .a3]
  | 5 => [.a2, .a5]
  | _ => []

/-- Selected source obligations plus distinct target additions. Documentation
and monitoring also occur in HAIP; "additional" is relative to this profile. -/
def referenceRoute : Route where
  source := [riskTest, inputEvidence, traceBinding]
  shared := [riskTest, inputEvidence, traceBinding]
  additional := [currentDocument, currentPlan]

theorem reference_route_has_real_shared_obligations :
    referenceRoute.shared ≠ [] ∧ linked referenceRoute = true := by decide

end Hiroshima

namespace BridgeExamples

private def context : Context := ⟨1, 1, 1, 1, 1⟩
private def scope : Scope := ⟨context, 1, 1⟩
private def good (q : Requirement) : Entry := ⟨q, scope, .operation, .supported, [1], []⟩
private def sourceEntries : List Entry := Hiroshima.referenceRoute.source.map good
private def completeEntries : List Entry := (targetRequirements Hiroshima.referenceRoute).map good
private def bundle (entries : List Entry) : Bundle :=
  ⟨Hiroshima.referenceRoute, scope, scope, entries⟩

/-- Concrete nonvacuous positive witness, not only an all-reject controller. -/
theorem complete_evidence_executes :
    runGate context context false true .allow (bundle completeEntries) = .executed := by decide

/-- Concrete separation: source succeeds but missing target additions cause HOLD. -/
theorem source_pass_is_not_target_pass :
    allSupported scope sourceEntries Hiroshima.referenceRoute.source = true ∧
      ready Hiroshima.referenceRoute scope scope sourceEntries = false ∧
      runGate context context false true .allow (bundle sourceEntries) = .held := by decide

theorem model_proof_cannot_replace_operation_evidence :
    entrySupports scope Hiroshima.riskTest
      { good Hiroshima.riskTest with observedStage := .model } = false := by decide

theorem no_implicit_restart :
    runGate context context true true .allow (bundle completeEntries) = .stopped := by decide

end BridgeExamples
end CrossFramework

end EUAIActMapping
