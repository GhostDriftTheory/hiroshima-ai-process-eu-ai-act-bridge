#!/usr/bin/env python3
"""Hiroshima AI Process -> Responsibility OS -> selected EU technical profiles.

Copyright (c) 2026 AI Assurance, Inc. All rights reserved. See README.md.
Python 3.11+, standard library only. No network requests or physical actuation.

  python haip_eu_poc_bridge.py --self-test
  python haip_eu_poc_bridge.py --poc ../coldchain-handoff-assurance/poc_handoff_pde.py
  python haip_eu_poc_bridge.py --self-test --poc ../coldchain-handoff-assurance/poc_handoff_pde.py
  python haip_eu_poc_bridge.py --poc ../coldchain-handoff-assurance/poc_handoff_pde.py --lean-project .

The external PoC is NOT copied, approximated or replaced. Its pinned source bytes
are checked before execution. The adapter calls its actual run_chain function.
Only an EXECUTED bridge outcome invokes the in-memory adoption sink. HOLD stops
this handoff chain; STOP additionally latches the controller's stopped state.

--input accepts {"handoffs": [...], "bridge": {...}}; see --example-input.
--json emits complete receipts, original input/output and scoped gaps to stdout.
--lean-project builds the exact mapping, then checks concrete normalized receipts
with Lean in a temporary file. Failure never silently becomes "verified".
The normalizer, Python, floating-point PoC, source authenticator and real-world
inputs are outside the universal Lean proof. Concrete correspondence is not a
universal refinement proof or a regulatory certificate.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import itertools
import json
import random
import shutil
import subprocess
import sys
import tempfile
import types
import unittest
from dataclasses import asdict, dataclass, replace
from enum import Enum
from pathlib import Path
from typing import Any, Iterable

POC_REPOSITORY = "GhostDriftTheory/coldchain-handoff-assurance"
POC_COMMIT = "1437b21a41b4c2b8623e8ae22ad71db3ef330383"
POC_GIT_BLOB = "6fefdf53348fa3fda5158bf7d9b8666e9fd4cfb0"
POC_SHA256 = "4fc65615fd383d3491f4ad931da90b77e49188709a03e3d46195cebc4569919f"
EXPECTED_LEAN_SHA256 = "52c956ab4a6225944f5a40528000996e54e8ec30b7c24b28cc84709760865761"
MAX_JSON_BYTES = 8_000_000
MAX_HANDOFFS = 1000
SCHEMA = "haip-eu-poc-bridge.v1"


class VerificationError(ValueError):
    """Input, source binding or requested verification failed."""


class Stage(str, Enum):
    MODEL = "model"
    IMPLEMENTATION = "implementation"
    OPERATION = "operation"


class Status(str, Enum):
    SUPPORTED = "supported"
    FAILED = "failed"
    UNKNOWN = "unknown"
    NOT_COVERED = "notCovered"
    NOT_ASSESSED = "notAssessed"
    NOT_APPLICABLE = "notApplicable"


class Request(str, Enum):
    ALLOW = "allow"
    WITHHOLD = "withhold"
    STOP = "stop"


class Decision(str, Enum):
    EXECUTED = "executed"
    HELD = "held"
    STOPPED = "stopped"


def natural(value: Any, label: str) -> int:
    if type(value) is not int or value < 0:
        raise VerificationError(f"{label}: expected a non-negative integer, not a bool")
    return value


@dataclass(frozen=True)
class Context:
    system: int
    release: int
    specification: int
    boundary: int
    documentation: int

    def __post_init__(self) -> None:
        for key, value in asdict(self).items():
            natural(value, f"context.{key}")


@dataclass(frozen=True)
class Scope:
    context: Context
    purpose: int
    actorRole: int

    def __post_init__(self) -> None:
        if not isinstance(self.context, Context):
            raise VerificationError("scope.context: expected Context")
        natural(self.purpose, "scope.purpose")
        natural(self.actorRole, "scope.actorRole")


@dataclass(frozen=True)
class Requirement:
    code: int
    stage: Stage = Stage.OPERATION

    def __post_init__(self) -> None:
        natural(self.code, "requirement.code")
        if not isinstance(self.stage, Stage):
            raise VerificationError("requirement.stage: expected Stage")


@dataclass(frozen=True)
class Entry:
    requirement: Requirement
    scope: Scope
    observedStage: Stage
    status: Status
    evidenceIds: tuple[int, ...]
    gapIds: tuple[int, ...]

    def __post_init__(self) -> None:
        if not isinstance(self.requirement, Requirement) or not isinstance(self.scope, Scope):
            raise VerificationError("entry requires typed requirement and scope")
        if not isinstance(self.observedStage, Stage) or not isinstance(self.status, Status):
            raise VerificationError("entry requires typed stage and status")
        if type(self.evidenceIds) is not tuple or type(self.gapIds) is not tuple:
            raise VerificationError("entry IDs must be immutable tuples")
        for value in (*self.evidenceIds, *self.gapIds):
            natural(value, "entry identifier")


@dataclass(frozen=True)
class Route:
    source: tuple[Requirement, ...]
    shared: tuple[Requirement, ...]
    additional: tuple[Requirement, ...]

    def __post_init__(self) -> None:
        for values in (self.source, self.shared, self.additional):
            if type(values) is not tuple or any(not isinstance(q, Requirement) for q in values):
                raise VerificationError("route requirements must be typed immutable tuples")

    @property
    def target(self) -> tuple[Requirement, ...]:
        return self.shared + self.additional


@dataclass(frozen=True)
class Bundle:
    route: Route
    sourceScope: Scope
    targetScope: Scope
    entries: tuple[Entry, ...]

    def __post_init__(self) -> None:
        if not isinstance(self.route, Route) or not isinstance(self.sourceScope, Scope) or not isinstance(self.targetScope, Scope):
            raise VerificationError("bundle requires a typed route and scopes")
        if type(self.entries) is not tuple or any(not isinstance(e, Entry) for e in self.entries):
            raise VerificationError("bundle entries must be a typed immutable tuple")


RISK, INPUT, TRACE, DOCUMENT, PLAN = (Requirement(i) for i in range(1, 6))
REFERENCE_ROUTE = Route((RISK, INPUT, TRACE), (RISK, INPUT, TRACE), (DOCUMENT, PLAN))
REFERENCE_SCOPE = Scope(Context(1, 1, 1, 1, 1), 1, 1)
VOCABULARY = {
    1: {"meaning": "PoC risk-test acceptance under its fixed starter profile", "haip": [1, 5], "eu": ["9(6)-(8), selected testing contribution"]},
    2: {"meaning": "PoC-required input evidence flags passed", "haip": [1, 5], "eu": ["9, selected evidence-use contribution"]},
    3: {"meaning": "input, output and exact PoC source are bound in a reproducible receipt", "haip": [3, 4, 10], "eu": ["12, selected trace contribution", "43, assessment evidence only"]},
    4: {"meaning": "document bytes match their digest and current context metadata", "haip": [1, 3], "eu": ["11(1), metadata binding only"]},
    5: {"meaning": "current document/plan binding and selected monitoring check passed", "haip": [2, 5], "eu": ["72(1)-(3), selected plan contribution"]},
}


def entry_supports(scope: Scope, req: Requirement, entry: Entry) -> bool:
    return (entry.requirement == req and entry.scope == scope
            and entry.observedStage == req.stage and entry.status == Status.SUPPORTED
            and len(entry.evidenceIds) > 0 and all(i != 0 for i in entry.evidenceIds)
            and len(entry.gapIds) == 0)


def supports(scope: Scope, entries: tuple[Entry, ...], req: Requirement) -> bool:
    return any(entry_supports(scope, req, entry) for entry in entries)


def all_supported(scope: Scope, entries: tuple[Entry, ...], requirements: Iterable[Requirement]) -> bool:
    return all(supports(scope, entries, req) for req in requirements)


def bridge_ready(bundle: Bundle) -> bool:
    r = bundle.route
    keys = [entry.requirement for entry in bundle.entries]
    return (bool(r.shared) and all(req in r.source for req in r.shared)
            and bundle.sourceScope == bundle.targetScope and len(set(keys)) == len(keys)
            and all_supported(bundle.sourceScope, bundle.entries, r.source)
            and all_supported(bundle.targetScope, bundle.entries, r.additional))


def structural_blockers(bundle: Bundle) -> tuple[str, ...]:
    """Explain non-evidence structural failures; missing lists alone are insufficient."""
    keys = [entry.requirement for entry in bundle.entries]
    reasons = []
    if not bundle.route.shared:
        reasons.append("EMPTY_SHARED_PROFILE")
    if any(q not in bundle.route.source for q in bundle.route.shared):
        reasons.append("UNMAPPED_SHARED_OBLIGATION")
    if bundle.sourceScope != bundle.targetScope:
        reasons.append("SOURCE_TARGET_SCOPE_MISMATCH")
    if len(keys) != len(set(keys)):
        reasons.append("DUPLICATE_REQUIREMENT_ENTRIES")
    return tuple(reasons)


def missing(scope: Scope, entries: tuple[Entry, ...], requirements: Iterable[Requirement]) -> tuple[Requirement, ...]:
    return tuple(req for req in requirements if not supports(scope, entries, req))


def gate(halted: bool, ready: bool, request: Request) -> Decision:
    if type(halted) is not bool or type(ready) is not bool or not isinstance(request, Request):
        raise VerificationError("gate accepts actual booleans and a Request enum only")
    if halted or request == Request.STOP:
        return Decision.STOPPED
    if request == Request.WITHHOLD or not ready:
        return Decision.HELD
    return Decision.EXECUTED


def run_gate(current: Context, event_context: Context, halted: bool, domain_ready: bool,
             request: Request, bundle: Bundle) -> Decision:
    if type(domain_ready) is not bool:
        raise VerificationError("domain_ready must be a bool, not an inferred truthy value")
    return gate(halted, domain_ready and bridge_ready(bundle)
                and bundle.targetScope.context == current and event_context == current, request)


def jsonable(value: Any) -> Any:
    if isinstance(value, Enum):
        return value.value
    if hasattr(value, "__dataclass_fields__"):
        return jsonable(asdict(value))
    if isinstance(value, dict):
        return {str(k): jsonable(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [jsonable(v) for v in value]
    return value


def canonical(value: Any) -> bytes:
    try:
        return json.dumps(jsonable(value), sort_keys=True, ensure_ascii=False,
                          separators=(",", ":"), allow_nan=False).encode("utf-8")
    except (TypeError, ValueError) as exc:
        raise VerificationError(f"non-canonical/non-finite evidence: {exc}") from exc


def digest(value: Any) -> str:
    return hashlib.sha256(canonical(value)).hexdigest()


def strict_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise VerificationError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def invalid_constant(value: str) -> None:
    raise VerificationError(f"non-finite JSON constant: {value}")


def parse_json(raw: str) -> Any:
    if len(raw.encode("utf-8")) > MAX_JSON_BYTES:
        raise VerificationError("JSON exceeds the input size limit")
    return json.loads(raw, object_pairs_hook=strict_object, parse_constant=invalid_constant)


def parse_context(value: Any) -> Context:
    keys = {"system", "release", "specification", "boundary", "documentation"}
    if not isinstance(value, dict) or set(value) != keys:
        raise VerificationError(f"context requires exactly {sorted(keys)}")
    return Context(**value)


def parse_scope(value: Any) -> Scope:
    if not isinstance(value, dict) or set(value) != {"context", "purpose", "actorRole"}:
        raise VerificationError("scope requires context, purpose, actorRole")
    return Scope(parse_context(value["context"]), natural(value["purpose"], "purpose"),
                 natural(value["actorRole"], "actorRole"))


def load_poc(path: Path) -> tuple[types.ModuleType, dict[str, str]]:
    """Execute the verified immutable source buffer, not a subsequently reopened path."""
    raw = path.read_bytes()
    if len(raw) > 1_000_000:
        raise VerificationError("unexpected PoC source size")
    # Git on Windows may use CRLF; only newline normalization is allowed.
    source = raw.replace(b"\r\n", b"\n")
    actual = hashlib.sha256(source).hexdigest()
    blob = hashlib.sha1(b"blob " + str(len(source)).encode("ascii") + b"\0" + source).hexdigest()
    if actual != POC_SHA256 or blob != POC_GIT_BLOB:
        raise VerificationError("PoC source differs from the pinned public revision; no code was executed")
    name = "_verified_coldchain_handoff_" + actual[:16]
    module = types.ModuleType(name)
    module.__file__ = str(path.resolve())
    sys.modules[name] = module  # Required by dataclasses in the external source.
    try:
        exec(compile(source, str(path.resolve()), "exec"), module.__dict__)
    except Exception:
        sys.modules.pop(name, None)
        raise
    return module, {"repository": POC_REPOSITORY, "commit": POC_COMMIT,
                    "git_blob": blob, "canonical_source_sha256": actual,
                    "local_file_sha256": hashlib.sha256(raw).hexdigest()}


def document_fixture(scope: Scope = REFERENCE_SCOPE) -> dict[str, Any]:
    text = "Synthetic reference document: cold-chain PoC profile v1; no regulatory certification."
    return {"context": jsonable(scope.context), "monitoringPlanVersion": 1,
            "content": text, "content_sha256": hashlib.sha256(text.encode()).hexdigest()}


def plan_fixture(scope: Scope = REFERENCE_SCOPE) -> dict[str, Any]:
    return {"context": jsonable(scope.context), "version": 1, "check": "poc-release-with-evidence-v1"}


def handoff_fixture() -> dict[str, Any]:
    return {"shipment_id": "DEMO-001", "measure_id": "lifescience.coldchain.handoff.2to8c.v1",
            "duration_minutes": 10, "temperatures": [[0, 5.0], [5, 5.2], [10, 5.1]],
            "temp_missing": False, "max_temp_sample_gap_minutes": 5,
            "handoff_from": "Shipper", "handoff_to": "Receiver",
            "evidence_ok": True, "custody_complete": True, "seal_intact": True,
            "logger_calibrated": True, "temp_records_complete": True}


def example_input() -> dict[str, Any]:
    return {"schema": SCHEMA, "handoffs": [handoff_fixture()], "bridge": {
        "current_scope": jsonable(REFERENCE_SCOPE), "source_scope": jsonable(REFERENCE_SCOPE),
        "target_scope": jsonable(REFERENCE_SCOPE), "event_context": jsonable(REFERENCE_SCOPE.context),
        "document": document_fixture(), "monitoring_plan": plan_fixture(),
        "request": "allow", "created_at": 0, "retain_until": 10}}


def make_bundle(payload: dict[str, Any], raw_handoff: dict[str, Any], source: Scope, target: Scope,
                document: Any, plan: Any) -> tuple[Bundle, dict[str, Any], dict[str, str]]:
    """Derive findings from actual PoC output and checked metadata, not a compliance flag."""
    artifacts: dict[str, Any] = {}
    explanations: dict[str, str] = {}

    def artifact(value: Any) -> int:
        key = digest(value)
        artifacts[key] = copy.deepcopy(value)
        return int(key, 16)

    trace = {"poc_source_sha256": POC_SHA256, "input": raw_handoff, "output": payload}
    trace_id = artifact(trace)
    label = payload["label"]
    if label not in {"RELEASE", "HOLD", "QA_REVIEW", "REJECT"}:
        raise VerificationError("unexpected external PoC disposition")
    metrics = payload["metrics"]
    flags = [metrics[k] for k in ("evidence_ok", "custody_complete", "seal_intact",
                                 "logger_calibrated", "temp_records_complete")]
    if any(type(flag) is not bool for flag in flags):
        raise VerificationError("PoC evidence flags must be actual booleans")
    input_ok = all(flags)
    trace_ok = (payload["shipment_id"] == raw_handoff["shipment_id"]
                and payload["measure_id"] == raw_handoff["measure_id"])
    if not trace_ok:
        raise VerificationError("PoC output identity does not match its actual input")

    risk_status = Status.SUPPORTED if label == "RELEASE" else (Status.UNKNOWN if label == "HOLD" else Status.FAILED)
    entries = [
        Entry(RISK, source, Stage.OPERATION, risk_status, (trace_id,), () if risk_status == Status.SUPPORTED else (1001,)),
        Entry(INPUT, source, Stage.OPERATION, Status.SUPPORTED if input_ok else Status.FAILED, (trace_id,), () if input_ok else (2001,)),
        Entry(TRACE, source, Stage.OPERATION, Status.SUPPORTED, (trace_id,), ()),
    ]
    explanations["1001"] = "PoC did not establish auto-release under the selected risk-test profile."
    explanations["2001"] = "At least one PoC-required evidence flag failed."

    doc_status, doc_gaps, doc_ids = Status.UNKNOWN, (4001,), ()
    doc_ok = False
    if document is not None:
        doc_id = artifact(document)
        doc_ids = (doc_id,)
        try:
            if not isinstance(document, dict) or set(document) != {"context", "monitoringPlanVersion", "content", "content_sha256"}:
                raise VerificationError("unexpected document fields")
            ctx = parse_context(document["context"])
            natural(document["monitoringPlanVersion"], "document.monitoringPlanVersion")
            text = document["content"]
            if not isinstance(text, str) or not text.strip() or len(text.encode()) > 1_000_000:
                raise VerificationError("document content missing or too large")
            if hashlib.sha256(text.encode()).hexdigest() != document["content_sha256"]:
                raise VerificationError("document content digest mismatch")
            if ctx != target.context:
                raise VerificationError("document context is not the target context")
            doc_ok, doc_status, doc_gaps = True, Status.SUPPORTED, ()
        except (VerificationError, TypeError, KeyError) as exc:
            doc_status, doc_gaps = Status.FAILED, (4002,)
            explanations["4002"] = str(exc)
    explanations["4001"] = "Current target-profile document evidence was not supplied."
    entries.append(Entry(DOCUMENT, target, Stage.OPERATION, doc_status, doc_ids, doc_gaps))

    plan_status, plan_gaps, plan_ids = Status.UNKNOWN, (5001,), ()
    if plan is not None:
        plan_ids = (artifact(plan),)
        try:
            if not isinstance(plan, dict) or set(plan) != {"context", "version", "check"}:
                raise VerificationError("unexpected monitoring plan fields")
            if parse_context(plan["context"]) != target.context:
                raise VerificationError("monitoring plan context mismatch")
            version = natural(plan["version"], "plan.version")
            if not doc_ok or version != document["monitoringPlanVersion"]:
                raise VerificationError("plan is not bound to the current valid document")
            if plan["check"] != "poc-release-with-evidence-v1":
                raise VerificationError("unknown monitoring check; no arbitrary check is executed")
            if not (label == "RELEASE" and input_ok):
                raise VerificationError("selected monitoring predicate flags this PoC result")
            plan_status, plan_gaps = Status.SUPPORTED, ()
        except (VerificationError, TypeError, KeyError) as exc:
            plan_status, plan_gaps = Status.FAILED, (5002,)
            explanations["5002"] = str(exc)
    explanations["5001"] = "Target-profile monitoring plan was not supplied."
    entries.append(Entry(PLAN, target, Stage.OPERATION, plan_status, plan_ids, plan_gaps))
    return Bundle(REFERENCE_ROUTE, source, target, tuple(entries)), artifacts, explanations


class Runtime:
    """In-memory adoption boundary, not a physical shipment controller."""
    def __init__(self, current: Context):
        self.current = current
        self.halted = False
        self.history: list[dict[str, Any]] = []  # newest first, as in Lean
        self.adoptions: list[str] = []
        self.prune_cutoffs: list[int] = []

    def attempt(self, payload: dict[str, Any], bundle: Bundle, artifacts: dict[str, Any],
                gaps: dict[str, str], event_context: Context, request: Request,
                created_at: int, retain_until: int) -> dict[str, Any]:
        natural(created_at, "created_at")
        natural(retain_until, "retain_until")
        if created_at > retain_until:
            raise VerificationError("created_at exceeds retention deadline")
        domain_ready = payload["label"] == "RELEASE"
        decision = run_gate(self.current, event_context, self.halted, domain_ready, request, bundle)
        result = {"original": bundle, "poc_output": copy.deepcopy(payload),
                  "current_context": self.current, "event_context": event_context,
                  "halted_before": self.halted, "request": request, "domain_ready": domain_ready,
                  "bridge_ready": bridge_ready(bundle), "decision": decision,
                  "structural_blockers": structural_blockers(bundle),
                  "target_context_matches": bundle.targetScope.context == self.current,
                  "event_context_matches": event_context == self.current,
                  "created_at": created_at, "retain_until": retain_until,
                  "source_missing": missing(bundle.sourceScope, bundle.entries, bundle.route.source),
                  "target_missing": missing(bundle.targetScope, bundle.entries, bundle.route.target),
                  "artifacts": copy.deepcopy(artifacts), "gap_explanations": dict(gaps)}
        # Snapshot the entire receipt BEFORE any side effect, without deduplication.
        result["receipt_sha256"] = digest(result)
        self.history.insert(0, result)
        self.halted = decision == Decision.STOPPED
        if decision == Decision.EXECUTED:
            self.adoptions.append(result["receipt_sha256"])  # the actual reference sink
        return copy.deepcopy(result)

    def prune(self, cutoff: int) -> None:
        natural(cutoff, "cutoff")
        self.prune_cutoffs.append(cutoff)
        self.history = [r for r in self.history if cutoff <= r["retain_until"]]

    def audit(self, now: int) -> list[dict[str, Any]]:
        natural(now, "audit time")
        if any(cutoff > now for cutoff in self.prune_cutoffs):
            raise VerificationError("an earlier prune cutoff exceeds this audit time")
        return copy.deepcopy([r for r in self.history if now <= r["retain_until"]])


def run_input(poc: types.ModuleType, envelope: dict[str, Any]) -> dict[str, Any]:
    if not isinstance(envelope, dict) or set(envelope) != {"schema", "handoffs", "bridge"} or envelope["schema"] != SCHEMA:
        raise VerificationError("input requires exactly schema, handoffs and bridge")
    handoffs, config = envelope["handoffs"], envelope["bridge"]
    if not isinstance(handoffs, list) or not (1 <= len(handoffs) <= MAX_HANDOFFS):
        raise VerificationError("handoffs must be a nonempty bounded list")
    keys = {"current_scope", "source_scope", "target_scope", "event_context", "document", "monitoring_plan", "request", "created_at", "retain_until"}
    if not isinstance(config, dict) or set(config) != keys:
        raise VerificationError("bridge configuration keys do not match --example-input")
    current, source, target = (parse_scope(config[k]) for k in ("current_scope", "source_scope", "target_scope"))
    # The expected role/use are independent contract inputs, not candidate overrides.
    if target.purpose != current.purpose or target.actorRole != current.actorRole:
        raise VerificationError("target role/use differs from the independently supplied current contract")
    event_context = parse_context(config["event_context"])
    request = Request(config["request"])
    created_at, until = natural(config["created_at"], "created_at"), natural(config["retain_until"], "retain_until")
    if created_at > until:
        raise VerificationError("invalid retention interval")
    runtime = Runtime(current.context)
    receipts: list[dict[str, Any]] = []
    for handoff in handoffs:
        if not isinstance(handoff, dict):
            raise VerificationError("handoff must be a JSON object")
        # No downstream leg is even evaluated after this bridge denies adoption.
        # Calling the actual pinned PoC retains its own validation and verdict order.
        results, _ = poc.run_chain([copy.deepcopy(handoff)], "CHARTER-HAIP-EU-BRIDGE-DEMO", True)
        if len(results) != 1:
            raise VerificationError("unexpected number of PoC results")
        payload = results[0].decision.canonical_payload()
        bundle, artifacts, gaps = make_bundle(payload, handoff, source, target,
                                              config["document"], config["monitoring_plan"])
        item = runtime.attempt(payload, bundle, artifacts, gaps, event_context, request, created_at, until)
        receipts.append(item)
        if item["decision"] != Decision.EXECUTED:
            break
    return {"schema": SCHEMA, "kind": "actual-poc-to-reference-adoption-boundary",
            "config_sha256": digest(config), "input_sha256": digest(envelope),
            "receipts": receipts, "evaluated": len(receipts), "not_evaluated": len(handoffs) - len(receipts),
            "adoption_count": len(runtime.adoptions), "adopted_receipt_ids": runtime.adoptions,
            "lean_correspondence": "NOT_RUN", "physical_execution": False,
            "legal_compliance_certification": False}


def demo_inputs() -> list[tuple[str, dict[str, Any], str, Decision, int]]:
    """Named synthetic inputs run against the real, pinned PoC implementation."""
    cases: list[tuple[str, dict[str, Any], str, Decision, int]] = []
    def add(name: str, envelope: dict[str, Any], poc_label: str, decision: Decision, adopted: int) -> None:
        cases.append((name, envelope, poc_label, decision, adopted))
    e = example_input(); add("complete_evidence", e, "RELEASE", Decision.EXECUTED, 1)
    e = example_input(); e["bridge"]["document"] = None
    add("source_pass_missing_target_document", e, "RELEASE", Decision.HELD, 0)
    e = example_input(); e["bridge"]["monitoring_plan"] = None
    add("source_pass_missing_target_plan", e, "RELEASE", Decision.HELD, 0)
    e = example_input(); e["bridge"]["document"]["context"]["documentation"] = 2
    add("stale_document", e, "RELEASE", Decision.HELD, 0)
    e = example_input(); e["bridge"]["document"]["content"] += " tampered"
    add("document_digest_mismatch", e, "RELEASE", Decision.HELD, 0)
    e = example_input(); e["bridge"]["monitoring_plan"]["version"] = 2
    add("plan_version_mismatch", e, "RELEASE", Decision.HELD, 0)
    e = example_input(); e["bridge"]["source_scope"]["purpose"] = 2
    add("source_use_mismatch", e, "RELEASE", Decision.HELD, 0)
    e = example_input(); e["bridge"]["event_context"]["release"] = 2
    add("stale_event_context", e, "RELEASE", Decision.HELD, 0)
    e = example_input(); e["handoffs"][0]["custody_complete"] = False
    add("poc_evidence_gap", e, "HOLD", Decision.HELD, 0)
    e = example_input(); e["handoffs"][0].update(temperatures=[[0, 8.5], [1, 8.5]], duration_minutes=1, max_temp_sample_gap_minutes=1)
    add("poc_qa_review", e, "QA_REVIEW", Decision.HELD, 0)
    e = example_input(); e["handoffs"][0].update(temperatures=[[0, 11], [1, 11]], duration_minutes=1, max_temp_sample_gap_minutes=1)
    add("poc_reject", e, "REJECT", Decision.HELD, 0)
    e = example_input(); e["bridge"]["request"] = "withhold"
    add("human_withhold", e, "RELEASE", Decision.HELD, 0)
    e = example_input(); e["bridge"]["request"] = "stop"
    add("human_stop", e, "RELEASE", Decision.STOPPED, 0)
    e = example_input(); bad = handoff_fixture(); bad["custody_complete"] = False
    e["handoffs"] = [handoff_fixture(), bad, {"malformed_tail": True}]
    add("chain_stops_before_downstream_evaluation", e, "HOLD", Decision.HELD, 1)
    e = example_input(); e["handoffs"] = [handoff_fixture(), handoff_fixture()]
    add("duplicate_occurrences_are_not_deduplicated", e, "RELEASE", Decision.EXECUTED, 2)
    return cases


def lean_context(c: Context) -> str:
    return "⟨" + ", ".join(str(v) for v in asdict(c).values()) + "⟩"


def lean_scope(s: Scope) -> str:
    return f"⟨{lean_context(s.context)}, {s.purpose}, {s.actorRole}⟩"


def lean_req(q: Requirement) -> str:
    return f"⟨{q.code}, .{q.stage.value}⟩"


def lean_list(values: Iterable[str]) -> str:
    return "[" + ", ".join(values) + "]"


def lean_bundle(b: Bundle) -> str:
    route = "⟨" + ", ".join(lean_list(lean_req(q) for q in qs)
                              for qs in (b.route.source, b.route.shared, b.route.additional)) + "⟩"
    entries = lean_list(
        f"⟨{lean_req(e.requirement)}, {lean_scope(e.scope)}, .{e.observedStage.value}, .{e.status.value}, "
        f"{lean_list(map(str, e.evidenceIds))}, {lean_list(map(str, e.gapIds))}⟩" for e in b.entries)
    return f"⟨{route}, {lean_scope(b.sourceScope)}, {lean_scope(b.targetScope)}, {entries}⟩"


def witness_source(receipts: list[dict[str, Any]]) -> str:
    lines = ["import EUAIActMapping", "open EUAIActMapping EUAIActMapping.CrossFramework", "namespace ConcretePoCWitness",
             "/- Concrete normalized observations only; no proof of the Python normalizer or physical events. -/"]
    for i, r in enumerate(receipts):
        b = r["original"]
        # Only typed values and internally computed hex digests enter generated Lean.
        lines += [f'def receiptDigest{i} : String := "{r["receipt_sha256"]}"',
                  f"def bundle{i} : Bundle := {lean_bundle(b)}",
                  f"example : ready bundle{i}.route bundle{i}.sourceScope bundle{i}.targetScope bundle{i}.entries = {str(r['bridge_ready']).lower()} := by decide",
                  f"example : missing bundle{i}.targetScope bundle{i}.entries (targetRequirements bundle{i}.route) = {lean_list(lean_req(q) for q in r['target_missing'])} := by decide",
                  f"example : runGate {lean_context(r['current_context'])} {lean_context(r['event_context'])} {str(r['halted_before']).lower()} {str(r['domain_ready']).lower()} .{r['request'].value} bundle{i} = .{r['decision'].value} := by decide"]
    lines.append("end ConcretePoCWitness")
    return "\n".join(lines) + "\n"


def verify_lean(project: Path, receipts: list[dict[str, Any]]) -> dict[str, Any]:
    mapping = project / "EUAIActMapping.lean"
    if not mapping.is_file():
        raise VerificationError("EUAIActMapping.lean was not found in the specified project")
    local_mapping = mapping.read_bytes()
    canonical_mapping = local_mapping.replace(b"\r\n", b"\n")
    if hashlib.sha256(canonical_mapping).hexdigest() != EXPECTED_LEAN_SHA256:
        raise VerificationError("Lean mapping is not the exact revision bound to this adapter")
    lake = shutil.which("lake")
    if not lake:
        raise VerificationError("Lean/Lake unavailable: requested correspondence check was NOT performed")
    source = witness_source(receipts)
    with tempfile.TemporaryDirectory(prefix="haip-eu-witness-") as tmp:
        path = Path(tmp) / "ConcretePoCWitness.lean"
        path.write_text(source, encoding="utf-8", newline="\n")
        commands = [[lake, "build", "EUAIActMapping"],
                    [lake, "env", "lean", "-DwarningAsError=true", "EUAIActMapping.lean"],
                    [lake, "env", "lean", "-DwarningAsError=true", str(path)]]
        for command in commands:
            result = subprocess.run(command, cwd=project, capture_output=True, text=True,
                                    encoding="utf-8", errors="replace", timeout=1800, check=False)
            if result.returncode != 0:
                raise VerificationError("Lean verification failed; not machine-checked:\n" + (result.stdout + result.stderr)[-12000:])
    return {"status": "PASSED", "concrete_receipts": len(receipts),
            "mapping_sha256": EXPECTED_LEAN_SHA256,
            "local_mapping_sha256": hashlib.sha256(local_mapping).hexdigest(),
            "witness_sha256": hashlib.sha256(source.encode()).hexdigest(),
            "method": "Lean kernel checks via decide; no native_decide"}


# Synthetic model tests are separated from actual-PoC integration tests.
class ModelTests(unittest.TestCase):
    def good_bundle(self) -> Bundle:
        entries = tuple(Entry(q, REFERENCE_SCOPE, Stage.OPERATION, Status.SUPPORTED, (1,), ())
                        for q in REFERENCE_ROUTE.target)
        return Bundle(REFERENCE_ROUTE, REFERENCE_SCOPE, REFERENCE_SCOPE, entries)

    def test_source_is_not_target(self) -> None:
        b = replace(self.good_bundle(), entries=self.good_bundle().entries[:3])
        self.assertTrue(all_supported(b.sourceScope, b.entries, b.route.source))
        self.assertFalse(bridge_ready(b))
        self.assertEqual(missing(b.targetScope, b.entries, b.route.target), (DOCUMENT, PLAN))

    def test_status_role_artifact_and_gap_boundaries(self) -> None:
        b = self.good_bundle()
        bad_entries = [replace(b.entries[0], status=s) for s in Status if s != Status.SUPPORTED]
        bad_entries += [replace(b.entries[0], observedStage=Stage.MODEL),
                        replace(b.entries[0], observedStage=Stage.IMPLEMENTATION),
                        replace(b.entries[0], evidenceIds=()), replace(b.entries[0], evidenceIds=(0,)),
                        replace(b.entries[0], gapIds=(1,))]
        for bad in bad_entries:
            with self.subTest(entry=bad):
                self.assertFalse(bridge_ready(replace(b, entries=(bad,) + b.entries[1:])))

    def test_duplicate_conflicting_entry_is_rejected(self) -> None:
        b = self.good_bundle()
        for status in (Status.SUPPORTED, Status.FAILED):
            self.assertFalse(bridge_ready(replace(b, entries=b.entries + (replace(b.entries[0], status=status),))))

    def test_no_empty_or_unmapped_bridge(self) -> None:
        b = self.good_bundle()
        for route in (replace(b.route, shared=()), replace(b.route, shared=(Requirement(99),))):
            self.assertFalse(bridge_ready(replace(b, route=route)))

    def test_scope_and_all_context_fields(self) -> None:
        b = self.good_bundle()
        for key in asdict(REFERENCE_SCOPE.context):
            other = replace(REFERENCE_SCOPE, context=replace(REFERENCE_SCOPE.context, **{key: 2}))
            self.assertFalse(bridge_ready(replace(b, sourceScope=other)))
        for key in ("purpose", "actorRole"):
            self.assertFalse(bridge_ready(replace(b, sourceScope=replace(REFERENCE_SCOPE, **{key: 2}))))

    def test_exhaustive_1536_gate_combinations(self) -> None:
        b = self.good_bundle()
        count = 0
        for mask, domain, halted, request, event_matches, scope_matches in itertools.product(
                range(32), (False, True), (False, True), tuple(Request), (False, True), (False, True)):
            entries = tuple(replace(e, status=Status.SUPPORTED if mask & (1 << i) else Status.UNKNOWN)
                            for i, e in enumerate(b.entries))
            test = replace(b, entries=entries,
                           sourceScope=b.sourceScope if scope_matches else replace(b.sourceScope, purpose=2))
            ctx = b.targetScope.context
            event = ctx if event_matches else replace(ctx, release=2)
            got = run_gate(ctx, event, halted, domain, request, test)
            expected = (Decision.STOPPED if halted or request == Request.STOP else
                        Decision.EXECUTED if request == Request.ALLOW and domain and mask == 31
                        and event_matches and scope_matches else Decision.HELD)
            self.assertEqual(got, expected)
            count += 1
        self.assertEqual(count, 1536)

    def test_additional_obligations_cannot_enable(self) -> None:
        b = self.good_bundle()
        for mask in range(32):
            entries = tuple(e for i, e in enumerate(b.entries) if mask & (1 << i))
            before = replace(b, entries=entries)
            after = replace(before, route=replace(before.route, additional=before.route.additional + (Requirement(99),)))
            self.assertFalse(bridge_ready(after) and not bridge_ready(before))

    def test_stop_latches_and_withhold_has_no_effect(self) -> None:
        b = self.good_bundle(); rt = Runtime(REFERENCE_SCOPE.context)
        payload = {"label": "RELEASE"}
        rt.attempt(payload, b, {}, {}, REFERENCE_SCOPE.context, Request.WITHHOLD, 0, 10)
        self.assertEqual(rt.adoptions, [])
        rt.attempt(payload, b, {}, {}, REFERENCE_SCOPE.context, Request.STOP, 0, 10)
        rt.current = replace(rt.current, release=2)
        r = rt.attempt(payload, b, {}, {}, rt.current, Request.ALLOW, 0, 10)
        self.assertEqual(r["decision"], Decision.STOPPED)
        self.assertEqual(rt.adoptions, [])

    def test_receipts_preserve_extra_unknown_findings(self) -> None:
        b = self.good_bundle()
        extra = Entry(Requirement(99), REFERENCE_SCOPE, Stage.OPERATION, Status.NOT_COVERED, (), (99,))
        b = replace(b, entries=b.entries + (extra,))
        rt = Runtime(REFERENCE_SCOPE.context)
        r = rt.attempt({"label": "RELEASE"}, b, {}, {}, REFERENCE_SCOPE.context, Request.ALLOW, 0, 10)
        self.assertEqual(r["original"], b)
        self.assertTrue(bridge_ready(b))  # Outside this profile is preserved, not counted as covered.
        self.assertEqual(r["original"].entries[-1].status, Status.NOT_COVERED)

    def test_retention_order_duplicates_and_future_cutoff(self) -> None:
        b = self.good_bundle(); rt = Runtime(REFERENCE_SCOPE.context)
        for deadline in (10, 10, 20):
            rt.attempt({"label": "RELEASE"}, b, {}, {}, REFERENCE_SCOPE.context, Request.ALLOW, 0, deadline)
        before = copy.deepcopy(rt.history)
        rt.prune(5); rt.prune(6)
        self.assertEqual(rt.audit(8), before)
        self.assertEqual(len(rt.history), 3)
        rt.prune(11)
        self.assertEqual(len(rt.audit(11)), 1)
        with self.assertRaises(VerificationError):
            rt.audit(10)

    def test_200_interleaved_history_sequences(self) -> None:
        rng = random.Random(20261010)
        b = self.good_bundle()
        for _ in range(200):
            actual, reference = Runtime(REFERENCE_SCOPE.context), Runtime(REFERENCE_SCOPE.context)
            for _ in range(15):
                choice = rng.randrange(3)
                if choice == 0:
                    deadline, q = rng.randrange(21), rng.choice(tuple(Request))
                    for rt in (actual, reference):
                        rt.attempt({"label": "RELEASE"}, b, {}, {}, REFERENCE_SCOPE.context, q, 0, deadline)
                elif choice == 1:
                    actual.prune(rng.randrange(11))
                else:
                    ctx = replace(REFERENCE_SCOPE.context, release=rng.randrange(1, 4))
                    actual.current = reference.current = ctx
            self.assertEqual(actual.audit(10), reference.audit(10))
            self.assertEqual(actual.halted, reference.halted)
            self.assertEqual(actual.adoptions, reference.adoptions)

    def test_input_types_json_and_intervals(self) -> None:
        for text in ('{"x":1,"x":2}', '{"x":NaN}', '{"x":Infinity}'):
            with self.assertRaises(VerificationError):
                parse_json(text)
        with self.assertRaises(VerificationError):
            Context(True, 1, 1, 1, 1)
        with self.assertRaises(VerificationError):
            gate(False, "false", Request.ALLOW)  # type: ignore[arg-type]
        with self.assertRaises(VerificationError):
            Runtime(REFERENCE_SCOPE.context).attempt({"label": "RELEASE"}, self.good_bundle(), {}, {},
                REFERENCE_SCOPE.context, Request.ALLOW, 11, 10)


POC_UNDER_TEST: types.ModuleType | None = None
POC_PATH_UNDER_TEST: Path | None = None


class IntegrationTests(unittest.TestCase):
    def setUp(self) -> None:
        if POC_UNDER_TEST is None:
            self.skipTest("external PoC not supplied; this is not an actual-PoC integration run")
        self.poc = POC_UNDER_TEST

    def test_15_actual_poc_scenarios(self) -> None:
        for name, envelope, label, decision, adoptions in demo_inputs():
            with self.subTest(scenario=name):
                report = run_input(self.poc, envelope)  # type: ignore[arg-type]
                self.assertEqual(report["receipts"][-1]["poc_output"]["label"], label)
                self.assertEqual(report["receipts"][-1]["decision"], decision)
                self.assertEqual(report["adoption_count"], adoptions)
                if name == "chain_stops_before_downstream_evaluation":
                    self.assertEqual(report["not_evaluated"], 1)
                if name.startswith("source_pass"):
                    r = report["receipts"][0]; b = r["original"]
                    self.assertTrue(all_supported(b.sourceScope, b.entries, b.route.source))
                    self.assertNotEqual(r["target_missing"], ())

    def test_real_poc_rejects_malformed_inputs(self) -> None:
        bads = [{"custody_complete": "false"}, {"temperatures": [], "temp_missing": False},
                {"temperatures": [[0, float("nan")]]}, {"measure_id": "wrong"}]
        for patch in bads:
            with self.subTest(patch=patch):
                e = example_input(); e["handoffs"][0].update(patch)
                with self.assertRaises(ValueError):
                    run_input(self.poc, e)  # type: ignore[arg-type]

    def test_document_gap_prevents_even_evaluating_bad_tail(self) -> None:
        e = example_input(); e["bridge"]["document"] = None; e["handoffs"].append({"malformed": True})
        r = run_input(self.poc, e)  # type: ignore[arg-type]
        self.assertEqual(r["evaluated"], 1)
        self.assertEqual(r["not_evaluated"], 1)
        self.assertEqual(r["adoption_count"], 0)

    def test_ambiguous_configuration_is_rejected(self) -> None:
        e = example_input(); e["bridge"]["unexpected_allow_override"] = True
        with self.assertRaises(VerificationError):
            run_input(self.poc, e)  # type: ignore[arg-type]
        e = example_input(); e["bridge"]["target_scope"]["actorRole"] = 2
        with self.assertRaises(VerificationError):
            run_input(self.poc, e)  # type: ignore[arg-type]

    def test_source_tampering_rejected_before_execution(self) -> None:
        assert POC_PATH_UNDER_TEST is not None
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "tampered.py"
            path.write_bytes(POC_PATH_UNDER_TEST.read_bytes() + b"\nraise RuntimeError('must not execute')\n")
            with self.assertRaises(VerificationError):
                load_poc(path)

    def test_receipt_digests_and_roundtrip(self) -> None:
        report = run_input(self.poc, example_input())  # type: ignore[arg-type]
        for receipt in report["receipts"]:
            body = {k: v for k, v in receipt.items() if k != "receipt_sha256"}
            self.assertEqual(receipt["receipt_sha256"], digest(body))
            self.assertEqual(parse_json(canonical(receipt).decode()), jsonable(receipt))
            for key, artifact in receipt["artifacts"].items():
                self.assertEqual(key, digest(artifact))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--poc", type=Path, help="local, pinned poc_handoff_pde.py; no auto-download")
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--input", type=Path, help="actual PoC handoffs plus explicit bridge contract")
    parser.add_argument("--example-input", action="store_true", help="print a synthetic input envelope as JSON")
    parser.add_argument("--json", action="store_true", help="emit complete receipts to stdout")
    parser.add_argument("--lean-project", type=Path, help="require build, strict source check and concrete Lean correspondence")
    args = parser.parse_args(argv)
    if args.example_input:
        print(json.dumps(example_input(), ensure_ascii=False, indent=2)); return 0
    global POC_UNDER_TEST, POC_PATH_UNDER_TEST
    try:
        source = None
        if args.poc:
            POC_UNDER_TEST, source = load_poc(args.poc)
            POC_PATH_UNDER_TEST = args.poc
        if args.self_test:
            suite = unittest.TestSuite((unittest.defaultTestLoader.loadTestsFromTestCase(ModelTests),
                                       unittest.defaultTestLoader.loadTestsFromTestCase(IntegrationTests)))
            result = unittest.TextTestRunner(verbosity=2).run(suite)
            if not result.wasSuccessful():
                return 1
            if not args.lean_project and not args.input:
                return 0
        if POC_UNDER_TEST is None:
            parser.error("supply --poc, or use --self-test / --example-input")
        reports = []
        if args.input:
            envelope = parse_json(args.input.read_text(encoding="utf-8"))
            reports.append({"scenario": "external-input", **run_input(POC_UNDER_TEST, envelope)})
        else:
            for name, envelope, _label, _decision, _adopted in demo_inputs():
                reports.append({"scenario": name, **run_input(POC_UNDER_TEST, envelope)})
        receipts = [r for report in reports for r in report["receipts"]]
        verification: Any = {"status": "NOT_RUN"}
        if args.lean_project:
            verification = verify_lean(args.lean_project.resolve(), receipts)
            for report in reports:
                report["lean_correspondence"] = "PASSED"
        output = {"schema": SCHEMA, "poc_source": source, "lean_verification": verification,
                  "input_kind": "user-supplied" if args.input else "synthetic-demonstration",
                  "technical_vocabulary": VOCABULARY, "scenarios": reports,
                  "boundary": "Selected technical evidence; not full HAIP/EU compliance, third-party certification or physical execution."}
        if args.json:
            print(json.dumps(jsonable(output), ensure_ascii=False, indent=2, allow_nan=False))
        else:
            print(f"Actual pinned PoC: {POC_REPOSITORY}@{POC_COMMIT}")
            for r in reports:
                last = r["receipts"][-1]
                print(f"{r['scenario']}: PoC={last['poc_output']['label']} / bridge={last['decision'].value.upper()} / adoptions={r['adoption_count']} / skipped={r['not_evaluated']}")
            print(f"Lean correspondence: {verification['status']}")
            print("Adoptions are in-memory reference operations, not physical shipments or legal certifications.")
        return 0
    except (VerificationError, ValueError, OSError, KeyError, TypeError, subprocess.TimeoutExpired) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
