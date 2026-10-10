# Hiroshima AI Process × Responsibility OS × EU AI Act

[![Lean verification](https://github.com/GhostDriftTheory/hiroshima-ai-process-eu-ai-act-bridge/actions/workflows/lean.yml/badge.svg)](https://github.com/GhostDriftTheory/hiroshima-ai-process-eu-ai-act-bridge/actions/workflows/lean.yml)

**From Hiroshima to Global AI Assurance — reusable technical evidence, without silent expansion of what it establishes.**

**Repository:** `GhostDriftTheory/hiroshima-ai-process-eu-ai-act-bridge`  
**Maintainer:** AI Assurance, Inc.  
**Architecture:** official Hiroshima AI Process materials → Responsibility OS → independently scoped EU technical profiles.

This revision adds an evidence-preserving, machine-checkable bridge to the existing
EU AI Act application. A common responsibility record can support different
frameworks, while each target retains its own requirements, actor role, intended
use, version context and unresolved obligations. The bridge controls adoption;
it does not merely put two policy names beside the same Boolean result.

**The starting point is the official Hiroshima AI Process itself**, not the
coverage of a private HAIP mapping or of one cold-chain example. The
[Responsibility OS Kernel](https://github.com/GhostDriftTheory/responsibility-os-kernel)
remains unchanged and industry-independent. The earlier HAIP mapping collection
is neither a dependency nor the boundary of this work. The cold-chain PoC is one
separate executable instantiation of the generic bridge.

> **Verification status — 10 October 2026:** GitHub Actions
> `Lean verification / verify` passed for commit `dc67c7b`.
> The workflow successfully built and checked `EUAIActMapping.lean`
> with Lean 4.26.0, passed all 18 Python tests, verified the pinned
> public PoC source, and completed the concrete PoC-to-Lean
> correspondence check.
> These results apply to the verified commit and do not establish
> full EU AI Act compliance or production-system safety.

This is an independent technical proposal. It is not an official G7/HAIP project,
Japanese-government/OECD/EU approval, an AISI-adopted standard, a conformity
assessment, or a claim that implementing HAIP automatically satisfies EU law.

## Architecture and maintained files

```text
Official HAIP Guiding Principles / Code of Conduct
       │ explicit, reviewable technical interpretation
       ▼
Responsibility OS Kernel — unchanged, generic
       │ scoped obligations + evidence roles + adoption boundary
       ▼
Source technical profile ── named shared obligations ──► Target technical profile
       │                                                   + target additions
       └──────── full evidence, scope and gaps preserved ───────────┘
                                   │
               EUAIActMapping.lean: transfer / non-upgrade /
                 execution / export / complete-receipt history
                                   │
               haip_eu_poc_bridge.py: actual pinned PoC call
                 → evidence normalization → reference adoption sink
                 → optional concrete-run Lean correspondence check
```

The published repository contains the following six files, preserving their paths:

```text
EUAIActMapping.lean             # Original EU proofs + CrossFramework extension
README.md                      # This document; new repository coordinates
haip_eu_poc_bridge.py           # Actual pinned PoC adapter, demos and tests
lakefile.toml                  # New project name; old exact dependency pins
lean-toolchain                 # Lean 4.26.0, unchanged baseline
.github/workflows/lean.yml    # Lean + Python + actual PoC / Lean correspondence CI
```

The new workflow builds the complete `EUAIActMapping` module with the unchanged
Responsibility OS Kernel. It also runs Python integration tests against the
SHA-256-checked public PoC at a fixed commit, and checks concrete PoC receipts
against Lean. These checks are meaningful **only if they pass for this commit**.
No new Python package, JSON fixture, mapping file, schema file or committed
witness artifact is required.

All pre-existing public Lean declaration names and proof bodies are preserved.
`import ResponsibilityOS` still imports the external pinned Kernel. No private
ADIC implementation, certificate-checker internals or physical controller is
included. These public reference structures do not define the limits of
Responsibility OS, its applications, or the company's technology portfolio.

## Direct normative starting point

The official sources are the [HAIP Guiding Principles](https://digital-strategy.ec.europa.eu/en/library/hiroshima-process-international-guiding-principles-advanced-ai-system)
and [Code of Conduct](https://www.mofa.go.jp/files/100573473.pdf), using the
30 October 2023 baseline. The Code is voluntary guidance for organizations
developing advanced AI systems; the broader guiding principles address AI actors
as applicable. Their scope is not identical to the system/role-specific EU
requirements. A cold-chain example does not establish that its participants are
within either instrument's legal or organizational scope.

The following is **our technical interpretation**, not an official mapping or a
claim to formalize every obligation. All eleven action identifiers are represented
by `CrossFramework.Hiroshima.Action`. An identifier's existence is not coverage.

| HAIP action; Code page | Source theme | Contribution in this revision | What is not established |
|---|---|---|---|
| 1; pp.2–3 | Lifecycle risk assessment and mitigation | Named risk-test/input-evidence obligations; evidence-derived adoption; current-context binding | Complete risk discovery, all risk classes, sufficient mitigation, independent external testing |
| 2; pp.3–4 | Post-deployment risks and incidents | Existing versioned monitoring checks plus preservation of full scoped receipts | Collection of absent events, an operational incident-response programme |
| 3; p.4 | Capabilities, limitations and transparency | Exact scope, evidence roles, source/target missing obligations and original entries remain inspectable | A complete model/system transparency report |
| 4; pp.4–5 | Responsible information sharing | Export must preserve both specified observation policies; source evidence is not relabelled as target coverage | Lawful disclosure, confidentiality clearance, actual authority reporting |
| 5; p.5 | Governance and risk-management policies | Published source/target obligations control adoption; changes cannot silently rewrite historical permission | Organizational responsibilities, training, policy adequacy |
| 6; p.6 | Security safeguards | Logical deny/stop is a selected control contribution only | Model-weight security, access authentication, cybersecurity completeness, physical safe stopping |
| 7; p.6 | Content authentication and provenance | **Not implemented by this profile** | Receipt/source hashes are not watermarking or AI-content authentication |
| 8; p.7 | Safety/security research and investment | Context: published research and test artifacts | Funding commitments, sustained investment or research-impact claims |
| 9; p.7 | Global challenges and public benefit | Context: one medical-logistics demonstration | Measured patient, environmental, equity or societal benefits |
| 10; pp.7–8 | International technical standards | A proposed interoperable evidence/adoption structure with explicit target additions | Formal standards-body adoption or official protocol status |
| 11; p.8 | Data quality, privacy and intellectual property | Input-evidence checks are a limited contribution | Privacy compliance, training-data quality/bias controls or IP clearance |

The source themes above paraphrase the official Code. The implementation choices
and limitations are ours. The [European Commission's HAIP announcement](https://digital-strategy.ec.europa.eu/en/news/commission-welcomes-g7-leaders-agreement-guiding-principles-and-code-conduct-artificial)
describes HAIP and EU legislation as complementary; that policy relationship is
not a proof of legal implication or of this particular implementation.

### What is reused, and what is checked again?

The generic bridge uses open, typed `Requirement` identifiers, not a fixed industry
ontology. An `Entry` separates the requirement, observed evidence stage, status,
artifact identifiers, material gaps and `Scope`. Scope includes the original five
context keys plus **intended use and actor role**. Exact equality is this reference
policy's conservative reuse rule, not a claim that legislation mandates it.

The executable example has three source obligations: acceptance of the PoC's
selected risk test, its required evidence flags, and binding of the input/output
trace to the pinned implementation. The EU target reuses those same three
technical obligations and adds current-document and monitoring-plan checks.
These additions are **additional to this source profile**, not requirements found
only in EU law: HAIP also addresses documentation and monitoring.

This gives a selected connection to [Article 9(6)–(8)](https://ai-act-service-desk.ec.europa.eu/en/ai-act/article-9)
(testing and predefined evaluation criteria), alongside the original six EU
profiles retained below. It is **not** a complete Article 9 risk-management system,
and no legal adequacy of the PoC thresholds is inferred. The checks use the
unchanged public starter profile; they do not replace product/lane validation.

The route is published configuration, not a permission chosen by an untrusted
candidate. A supported entry must have the correct scope and evidence stage,
nonempty nonzero artifact IDs, and no material gap. Duplicate requirement entries
invalidate transfer, including conflicting favourable/adverse duplicates.
`unknown`, `failed`, `notCovered`, `notAssessed` and `notApplicable` do not satisfy
a required check. Not-applicable obligations must be excluded through a justified
profile decision, not treated as evidence of passing them. Findings outside the
selected profile remain in the raw receipt and are never counted as covered.

## New machine-checkable statements

All names in this section have the prefix `EUAIActMapping.CrossFramework.`.
These describe the supplied propositions/proofs; the new revision's build status
is explicitly stated above.

| Statement | Declaration / construction | Nontrivial boundary |
|---|---|---|
| Shared technical guarantees are inherited | `source_guarantee_inherited` | Derives shared support from source support **and an explicit inclusion**; does not assume the desired target conclusion |
| The target's evidence is derived | `target_evidence_is_derived` | Requires source/target scope agreement, a nonempty mapped bridge, unambiguous evidence, and separately checked target additions |
| Source success cannot fill a target gap | `missing_target_blocks_transfer`, `missing_target_never_executes` | Applies to missing shared **or** additional obligations; no aggregate compliance score |
| Model proofs do not become operation evidence | `wrong_evidence_stage_rejected`, `evidence_without_artifacts_rejected`, `material_gap_rejected` | Stage, artifact presence and unresolved material gaps are checked independently |
| Stronger targets cannot enable a blocked transfer | `additional_requirements_cannot_enable` | Extending target obligations only restricts this route; it never manufactures coverage |
| Execution uses the evidence-derived gate | `runGate_is_capture`, `executed_requires_bridge`, `executed_requires_target_evidence` | Reuses the original `capture`/`gate`; checks domain readiness, current context, role/use scope and target evidence |
| New records inherit existing recording/retention and stop semantics | `evidence_gated_record_is_retained`, `evidence_gate_cannot_restart` | No replacement controller or Kernel, and no physical safe-stop assertion |
| Whole evidence and gap history survives interleavings | `Audit.run_without_pruning`, `Audit.history_transfer_and_preservation` | Exact live **receipt-list equality** with a no-deletion run, including original entries, scope, missing lists, order and repeated occurrences |
| Receipts stay connected to the original record list | `Audit.run_synchronized` | Preserves equality between receipt-record projections and the original operational history, from a synchronized initial state |
| Both frameworks' evidence distinctions survive export | `joint_policy_preservation_iff`, `recoverable_export_preserves_both` | Two independently supplied observation policies; a round-trip exporter is sufficient, not mandatory |

`BridgeExamples.complete_evidence_executes` supplies a concrete positive case.
`BridgeExamples.source_pass_is_not_target_pass` supplies a concrete source-pass /
target-HOLD separation. Additional examples cover stage substitution and stopped
controllers. The original Kernel-based nonempty trace-policy example and its
operation-only counterexample remain unchanged.

### Whole-history result, not just one successful case

`Audit.Command` interleaves evidence-bearing attempts, retention filtering and
profile changes. `Audit.run_valid` derives that every surviving receipt keeps its
source/target missing lists and that any executed record had target support in
its **captured historical** role, use and context. Profile changes do not reissue
an old assessment as a current one.

`Audit.run_without_pruning` proves the complete live receipt list agrees with a
no-deletion reference run under the explicit condition that every intermediate
pruning cutoff is no later than the final audit cutoff. This is equality of the
whole structured receipts, not equality of final decisions, membership alone or
just a count. `Audit.run_synchronized` connects these richer receipts to the
original record list. Starting with both lists empty satisfies synchronization;
arbitrary preloaded histories must separately justify their invariants.

The reference gate does not depend on deleted history. The result cannot be
silently reused for a different controller that does. The retention deadlines and
clock are supplied assumptions, not a legal deadline calculator.

## Actual PoC connection — one optional Python file

`haip_eu_poc_bridge.py` verifies and loads the existing
[Cold-Chain Handoff Assurance PoC](https://github.com/GhostDriftTheory/coldchain-handoff-assurance/tree/1437b21a41b4c2b8623e8ae22ad71db3ef330383),
then calls its actual `run_chain` function for each handoff submitted to the
bridge. It does not imitate the PoC's decision rules or ship another copy of them.

The external source is pinned to:

```text
Repository: GhostDriftTheory/coldchain-handoff-assurance
Commit:     1437b21a41b4c2b8623e8ae22ad71db3ef330383
File:       poc_handoff_pde.py
Git blob:   6fefdf53348fa3fda5158bf7d9b8666e9fd4cfb0
SHA-256:    4fc65615fd383d3491f4ad931da90b77e49188709a03e3d46195cebc4569919f
```

Both hashes are checked before executing the verified in-memory source buffer.
CRLF→LF normalization is allowed for Windows checkouts; the original local-byte
hash is also reported. A different source revision is rejected. There are no
network calls and no permissive “skip source verification” option.

The adapter records the actual input and PoC output, source binding, normalized
entries, scope, missing obligations and metadata-check explanations. It checks
actual document bytes against their stated digest, current document context,
document/plan version agreement, and one explicit monitoring predicate. These
are substantive **consistency checks**, not evaluation of all required document
contents or an assertion that supplied evidence flags are authentic.

The bridge calls its **in-memory adoption sink only after an `EXECUTED` result**.
It does not merely print a preferred verdict. On HOLD or STOP, no downstream
handoff is evaluated; STOP also latches the stopped state. The original PoC
`RELEASE / HOLD / QA_REVIEW / REJECT` is preserved separately. In particular,
PoC `REJECT` blocks this candidate but is not reinterpreted as a permanent
emergency stop of every future operation.

Observed examples from the actual pinned implementation on **synthetic data**:

| Scenario | Actual PoC result | Bridge outcome | Reference adoptions |
|---|---|---|---:|
| Complete selected evidence | `RELEASE` | `EXECUTED` | 1 |
| Source profile passes; target document missing | `RELEASE` | `HELD` | 0 |
| Source profile passes; target plan missing | `RELEASE` | `HELD` | 0 |
| Stale document or mismatched plan version | `RELEASE` | `HELD` | 0 |
| Required custody evidence missing | `HOLD` | `HELD` | 0 |
| PoC gray zone / fatal breach | `QA_REVIEW` / `REJECT` | `HELD` | 0 |
| Human stop | `RELEASE` | `STOPPED` | 0 |
| First leg passes, second fails, third is malformed | `HOLD` at second leg | `HELD`; third never evaluated | 1 |

### Connection to Lean, and exactly what remains outside

With `--lean-project`, the adapter checks the exact mapping-source digest, builds
`EUAIActMapping`, runs its warning-as-error source check, and creates a temporary
Lean file containing concrete statements for every normalized receipt. Lean checks
**bridge readiness, the exact target-missing list and the gate outcome** using
`by decide`, not `native_decide`. The temporary source is removed afterward;
its digest and the mapping digest are reported. Missing tools or any failed
command return a nonzero exit status, never a successful verification label.

This crosses three distinct levels:

1. The universal Lean propositions describe the formal bridge and its histories.
2. The actual pinned Python PoC runs on supplied inputs; the adapter controls the
   local reference adoption sink and preserves its evidence.
3. The optional concrete Lean check compares those normalized observations to
   the formal definitions for that run.

Level 3 **passed in GitHub Actions for commit `dc67c7b`**.
This is a concrete correspondence check, not a universal proof of the
Python normalizer, the external PoC's floating-point calculations,
hashing, sensor truth, human authority or a production runtime.
Receipt hashes bind bytes; they are not signatures, authenticated
timestamps, content provenance standards, or one-use execution tokens.
The implementation performs no real shipment, actuator, external API
or production-system write.

### Executed tests for this delivery

The provided Python file passed **18 test methods**, including **15 actual-PoC
integration scenarios**, **1,536 exhaustive gate combinations**, and **200
reproducible interleaved-history sequences**. The suite also checks malformed
inputs, source tampering before execution, conflicting duplicate entries,
stage substitution, missing artifacts, stale scope, future-dated pruning,
receipt round-trips and preservation of repeated occurrences.

These are runtime test results, not a Lean build result or independent third-party
validation. Running `--self-test` without `--poc` explicitly skips the external
integration tests rather than presenting them as completed.

## Preserved EU application layer

The following six-article profiles and history results predate the new bridge.
Their existing declaration and proof bodies are retained unchanged. The bridge
above is additive; its source-to-target transfer is not inferred from the article
labels in this earlier table.

## What the mapping establishes

Article numbers identify **selected technical contributions**, not proofs that an
entire article or a deployed AI system is legally satisfied. All declaration
names below are prefixed by `EUAIActMapping.`.

The table separates the **legal requirement**, **our reference design choice**,
**the formal proposition** and **what still needs external assessment**.
Requirements are paraphrased from the selected subject matter of the original
[Regulation (EU) 2024/1689](https://eur-lex.europa.eu/eli/reg/2024/1689/oj/eng),
not a claim to encode every subsequent amendment. Article links lead to the
Commission's Service Desk; its update notices must be read with the text.

| Legal source and selected requirement | Reference predicate / design rationale | Lean declarations | Outside this profile |
|---|---|---|---|
| [Art.11(1)](https://ai-act-service-desk.ec.europa.eu/en/ai-act/article-11): prepare technical documentation before placing on the market or putting into service, and keep it current. | `Art11.supportsRecord` binds document, event and profile context, preventing use of mismatched documentation as current support. Exact key equality is our conservative implementation choice, not statutory wording. | `Art11.document_binding_is_exact`, `Art11.stale_document_is_rejected`; the normal-record implication in `history_evidence_chain`. | Document preparation timing, authenticity, actual contents, Annex IV completeness and legal sufficiency. |
| [Art.12(1)–(2)](https://ai-act-service-desk.ec.europa.eu/en/ai-act/article-12): enable automatic event logging over the system lifetime, including events useful for monitoring and risk-related traceability. | `advance` records every supplied attempt. `History.SameAt` relates an interleaved run to a full-history reference run, so retention processing cannot silently change the final live sequence. | `Art12.every_step_is_recorded`, `Art12.standard_trace_preserves_policy`, `History.run_without_pruning`. | Completeness of real event capture, whether recorded fields cover relevant risks, biometric-specific requirements and durable storage. |
| [Art.14(4)(d)–(e)](https://ai-act-service-desk.ec.europa.eu/en/ai-act/article-14): enable the assigned person to disregard/override/reverse outputs and to intervene or stop safely, as appropriate. | `gate` gives logical stop priority and prevents execution after withholding. `History.Permission` refers to the context recorded at execution; profile changes do not restart a stopped controller. | `Art14.withhold_never_executes`, `Art14.stop_always_halts`, `History.run_permission`, `History.stopped_run_stays_stopped`. | Human identity/authority, usability, competence, reversal of physical effects and actual safe stopping. The no-restart policy is our reference choice. |
| [Art.19(1)](https://ai-act-service-desk.ec.europa.eu/en/ai-act/article-19): retain provider-controlled automatic logs for the applicable purpose-appropriate period, with a six-month minimum unless applicable law provides otherwise. | `Art19.pruneExpired` applies an externally justified deadline. `History.CutoffsWithin` excludes deletion using a cutoff later than the final audit time. | `Art19.no_early_deletion`, `History.prune_twice`, `History.run_without_pruning`, `History.future_cutoff_counterexample`. | Selecting lawful deadlines, calendar-month conversion, provider control, exceptions, retention extensions and storage availability. No fixed day-count is substituted for months. |
| [Art.43](https://ai-act-service-desk.ec.europa.eu/en/ai-act/article-43): follow the applicable conformity-assessment procedure; the route depends on the system and applicable conditions. | `ResponsibilityOS.PreservesPolicy` describes evidence distinctions that an assessment view must retain under a supplied policy. A left inverse is a sufficient technical construction, not a legal obligation. | `Art43.recoverable_export_preserves_policy`, `Art43.backward_audit_factorization`; the per-record export conclusion in `history_evidence_chain`. | Selection/performance of the assessment procedure, acceptance by an assessor, completeness of evidence, actual exporter correctness and execution replay. |
| [Art.72(1)–(3)](https://ai-act-service-desk.ec.europa.eu/en/ai-act/article-72): establish documented post-market monitoring, collect/document/analyse relevant data systematically, and include the monitoring plan in technical documentation. | `Art72.passesPlan` binds the current document, its referenced plan and the supplied check. The history theorem classifies all final live records without losing order or duplicate occurrences through preceding retention steps. | `Art72.monitoring_complete`, `Art72.monitoring_preserves_occurrences`, `Art72.unmatched_plan_flags_all`, `Art72.outdated_document_flags_all`, `history_evidence_chain`. | Active collection of missing data, adequacy of risk checks, organisational follow-up, mandatory plan contents and analysis of interactions with other systems. |

The cross-article connection is not based only on naming: Art.12(2)(b) expressly
connects logging to Art.72 monitoring, Art.19(1) refers to Art.12 logs, and
Art.72(3) connects the plan to technical documentation. [Recital 71](https://ai-act-service-desk.ec.europa.eu/en/ai-act/recital-71)
also explains the roles of records and documentation in traceability, assessment
and monitoring. These references motivate the architecture; they do **not**
prove that our chosen predicates are legally sufficient. The correspondence is
explicit and reviewable; Lean checks the model, not the legal adequacy of this
interpretation.

### Strengthening Articles 11 and 72

`Art11.Documentation` explicitly binds document metadata to `Context` and records
`monitoringPlanVersion`. `Context.documentation` already identifies the document
version; it is reused rather than duplicated. The support check rejects a document
whose version is not the current profile's version. An old record can still be
valid evidence for its **historical** context; the check prevents silent reuse as
current evidence.

`Art72.MonitoringPlan` adds only its context, version and supplied check.
`passesPlan` checks the plan against the current profile and the document's plan
reference, checks the document/event/profile binding, then applies that check.
`normalRecords` and `reviewRecords` form an exhaustive, mutually exclusive
classification of the **supplied history**, with occurrence-count preservation.
Even an always-true supplied check cannot clear records under a mismatched plan
version or outdated document. “Normal” means this selected profile's checks
passed, **not** that the system is safe or legally compliant.

These are public reference-model checks, not an implementation of the document's
contents or a claim that its version identifiers are authentic. The new document
check is used for evidence support and monitoring; it does **not** add a separate
production document-loading gate to `advance`.

### One evidence chain

`evidence_chain` uses **one captured record** for document/context consistency,
recording/retention, necessary execution permission, policy-preserving export,
exclusive monitoring classification and review on a failed supplied check.
It has explicit event/document-context, retention and export-round-trip premises.
It does **not** assume the monitoring plan version matches: mismatches result in
review. The strengthened theorem takes document and plan arguments; the older
`Art72.reviewQueue` helpers remain available, but the integrated theorem now uses
the plan-bound partition.

The original positive witness uses the kernel's nonempty `traceA`/`traceB`
relevance policy. Its negative witness shows that an operation-only view loses
that distinction. An empty policy is not treated as evidence of coverage.

### History-wide evidence chain

The existing `evidence_chain` and all previous public declarations remain intact.
`History.Command` adds only `attempt`, `prune` and `reprofile`; the first two reuse
`advance` and `Art19.pruneExpired`, while the last changes the profile without
clearing history or the stopped flag. Commands are processed in supplied order;
records remain newest-first, as in the original model. Authorisation of profile
updates is external to this reference runner.

`History.run_without_pruning` proves a relational invariant over **arbitrary finite
command sequences**. Provided every intermediate pruning cutoff is no later than
the final audit cutoff, the actual run and the no-deletion reference run have the
same final profile and stopped flag, and **exactly the same final live record list**.
This is list equality, not merely membership or a count: order and repeated
occurrences are preserved. The record-retention result is derived through the
interleaved transitions, not supplied as a premise.

`history_evidence_chain` starts from an empty history and combines that invariant
with execution-time permission, current document support for normal records,
exclusive monitoring classification, review on any failed plan predicate, and
preservation of each retained trace's policy-relevant distinctions by an export
satisfying the stated round-trip law. `History.run_permission` also supports a
nonempty initial history when its permission invariant has already been established.
No assumption says that all records execute or pass monitoring.

**Historical permission and current evidence support are different.** An earlier
executed record retains the profile context captured at that time. After a profile
change, a record mismatching the current document/profile is reviewed rather than
silently recertified; the theorem does not retrospectively invalidate that earlier
execution. Nor does it make document loading a prerequisite of `advance`.

`History.live_execution_survives_pruning` supplies a positive execution case.
`History.future_cutoff_counterexample` shows why the time premise matters: pruning
at a record's deadline plus one can erase a record that would still be retained
at its deadline. `History.stopped_run_stays_stopped` covers every command suffix,
including profile changes. These are reference-model results, not deployment tests.

For a concrete reference scenario, record an allowed operation under context A
with retention deadline 10, prune at 5, switch to B, record an allowed operation
under B with deadline 20, and prune at 6. At audit cutoff 8, both records remain;
a current B document/plan with a successful check can classify the B record as
normal, but must review the A record. This illustrates prevention of evidence
loss and stale-context reuse, not a measured reduction in audit labour.

The reference control decision does not depend on the pruned history. A deployed
controller that does depend on it needs a separate correspondence/refinement
argument; the theorem does not silently cover a different transition function.

## GitHub setup — 日本語

リポジトリ **`hiroshima-ai-process-eu-ai-act-bridge`** は公開済みで、上記6ファイルを
所定の構造で配置しています。ワークフローの場所は
**`.github/workflows/lean.yml`** です。既存のKernelや既存リポジトリは
書き換えていません。`lakefile.toml`は新しいプロジェクト名を使用し、
Kernel/mathlibの版を従来どおり固定しています。

新しい横断保証は同じLeanファイル内の独立名前空間に追加しています。
既存6条項の定義・証明は維持し、広島AIプロセスの公式文書を起点とした技術的解釈を
責任OSに接続しています。従来の広島AIプロセス対応マッピングや、コールドチェーン
という一つの業務に責任OSの対象範囲を限定する変更ではありません。

**2026年10月10日のGitHub Actions（コミット `dc67c7b`）において、
Lean4のビルド、警告をエラー扱いとするソース検証、公開PoCのハッシュ検証、
Pythonの18テスト、および実際のPoC結果とLean形式モデルの照合が
すべて成功しました。**

検証結果は当該コミットを対象とするものであり、
EU AI Actへの全面準拠や実運用環境の安全性を証明するものではありません。

### Leanの検証

リポジトリ直下で、既存環境と同じコマンドです。

```sh
lake update
lake exe cache get
lake build EUAIActMapping
lake env lean -DwarningAsError=true EUAIActMapping.lean
```

Actionsが有効なら、push・pull requestで新規リポジトリの `Lean verification` が動きます。
新CIではLeanのビルドと厳格検証に加え、公開PoCの固定版の取得・ハッシュ検証、
Python統合テスト、具体的なPoC結果とLeanの照合まで実施します。
手動の場合は **Actions → Lean verification → Run workflow** です。

### 単一Pythonファイルのテストと実PoC接続

Python 3.11以上、追加ライブラリ不要です。

```sh
# 外部PoCなしのモデルテスト。実PoCテストは明示的にskipされます。
python haip_eu_poc_bridge.py --self-test

# 既存PoCファイルを指定すると、そのコードを実行した統合テストも行います。
python haip_eu_poc_bridge.py --self-test --poc ../coldchain-handoff-assurance/poc_handoff_pde.py

# 実PoCを使う15シナリオの実行結果を表示します。
python haip_eu_poc_bridge.py --poc ../coldchain-handoff-assurance/poc_handoff_pde.py

# Leanの準備後、同じ実行結果を形式定義と具体的に照合します。
python haip_eu_poc_bridge.py --poc ../coldchain-handoff-assurance/poc_handoff_pde.py --lean-project .
```

外部PoCのローカルファイルが必要です。新規取得する場合の例：

```sh
git clone --no-checkout https://github.com/GhostDriftTheory/coldchain-handoff-assurance.git ../coldchain-handoff-assurance
git -C ../coldchain-handoff-assurance checkout 1437b21a41b4c2b8623e8ae22ad71db3ef330383
```

すでに持っている場合は、その `poc_handoff_pde.py` のパスを `--poc` に指定します。
コードの一致は実行前に検査されます。外部PoCは今回の配布物へ複製していません。

`--json` を付けると入力・出力・証拠・不足事項を含む完全なレシートを標準出力へ
出します。実データの場合、共有前に内容を確認してください。機密情報の自動秘匿化は
行いません。独自入力は `--example-input` で形式を確認して `--input` で渡せます。
出力を保存する場合だけリダイレクト等を使い、生成JSONやLean witnessをリポジトリで
恒常的に管理する必要はありません。

CLIの参照実行は、メモリ内の採用処理までです。本番実行への接続では、入力・文書・
人の権限・時刻・設定の真正性、ゲート迂回防止、安全な停止先等を別途成立させる必要が
あります。実PoCとの接続ができたことと、実物流の本番運用が検証済みであることは別です。

## Verification baseline and reproducibility

The new dependency files preserve the earlier exact pins:

```text
Kernel:    9b4e7d25572f3a1e114508bdf1a2d62349e83993
mathlib:   2df2f0150c275ad53cb3c90f7c98ec15a56a1a67
Toolchain: leanprover/lean4:v4.26.0
```

The new workflow builds and checks the entire application source with warnings
as errors. It also runs Python model/integration tests with the exact public PoC
source and checks concrete receipts against Lean. It does not perform a separate
`#print axioms` audit or upload an audit report. All workflow checks passed
on GitHub Actions for commit `dc67c7b` on 10 October 2026. The verification
result is available at:
https://github.com/GhostDriftTheory/hiroshima-ai-process-eu-ai-act-bridge/actions/runs/38008866045
The supplied extension contains no `sorry`, `admit`, new `axiom`, `unsafe`
definition or `native_decide`. That source observation is not a substitute for
compilation or a dependency-wide trust analysis.

The adapter also binds the exact delivered `EUAIActMapping.lean` SHA-256 in
`EXPECTED_LEAN_SHA256` (after CRLF→LF normalization for Windows; the local-byte
hash is reported separately). Intentional changes to the Lean file require an explicit
adapter-pin update and a new build/correspondence check. Do not remove the check
to make a changed revision appear verified. The verification source is read and
checked separately from the externally pinned PoC source.

Lake resolves transitive dependencies into `lake-manifest.json` during the build.
Keep that resolved manifest and exact source revisions when recording a reproduced
verification environment; this workflow does not upload the manifest.
Use the commands above only with authorization under the License below.

The EU baseline remains the selected technical subject matter of the originally
adopted **Regulation (EU) 2024/1689**, not a continuously updated legal service.
The Commission's [Article 9](https://ai-act-service-desk.ec.europa.eu/en/ai-act/article-9)
and [Article 11](https://ai-act-service-desk.ec.europa.eu/en/ai-act/article-11) pages
consulted for this revision identify a 27 July 2026 consolidated-text baseline.
This work does not encode every amendment, application date, assessment route or
Annex IV content requirement. Source-to-predicate interpretation and applicable
law must still be reviewed for an actual deployment.

## License

© 2026 AI Assurance, Inc. All rights reserved.

No license is granted to use, copy, modify, distribute, sublicense, or create
derivative works from the source code in this repository except with prior
written permission from the copyright holder.

This reservation does not restrict rights arising under applicable law or
[GitHub's Terms of Service](https://docs.github.com/en/site-policy/github-terms/github-terms-of-service),
including their provisions for public repositories. Third-party dependencies
remain governed by their respective licenses; this notice does not relicense them.
No patent license is granted by this notice.

## Interpretation and deployment boundary

The legal-to-formal interpretation is external. The baseline is the selected
technical subject matter of Regulation (EU) 2024/1689, as originally adopted,
not a version-certified map of every current amendment. The Commission's Service
Desk pages include amendment/update notices; the table above is limited to the
stated original-baseline subject matter. Consult the applicable official
consolidated text and the relevant assessment route before using it for a deployment.
No application dates, conformity-assessment route or calendar-month conversion
are encoded here. [Annex IV](https://ai-act-service-desk.ec.europa.eu/en/ai-act/annex-4)
contains document-content requirements beyond this metadata model.

The model does not establish complete technical documentation, complete real-world
event capture, authentic version keys, suitable risk checks, correct retention
deadlines, durable storage, usable human interfaces, actual safe stopping or
organizational follow-up. History partitioning does not prove active collection
of events that were never supplied. Exact context equality is a conservative
reference policy, not a claim that the Act requires this exact data structure.

The kernel's faithfulness is not automatic logging, and its unique backward-audit
factorization is not executable replay. The logical `executed` outcome is not a
claim of physical execution. Actual deployment must prevent gate bypass, bind
authentic inputs to the model and connect logical stop to a justified safe-state
mechanism. Article 43 mapping supports inspectable assessment evidence; it does
not perform conformity assessment or assume that every assessment uses a third
party. These are limits of this **minimal public profile**, not limits on the
scope of Responsibility OS or its possible applications.

