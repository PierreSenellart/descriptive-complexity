#!/usr/bin/env python3
"""Generate the NP catalog submission for the Lax archive.

Reads the library at a tag, finds every problem proved NP-complete in the
usual shape (a bundled problem over a predicate, a `Σ₁` definition for
membership, a reduction from an earlier problem for hardness), and writes a
submission folder that builds on the registered NP core: the export file for
lax-export, one concept module per family of problems (the library's
definitions, restated by lax-export's skeleton, plus the problems and the
claims), and the bridge proofs. The prose of a concept module comes from the
library's own module docstring; `catalog.yaml` in the output folder may
override a family's title and description.

    lax/catalog.py --out lax/np-catalog [--library .] [--ref v1.2.2]
                   [--lax-export ~/git/software/lax-export] [--core lax/np-core]

The output folder is the one `lax init` made (its manifest gives the id).
Everything the generator writes is regenerated on the next run; the hand
side lives in the library's docstrings and in `catalog.yaml`.
"""
import argparse
import json
import os
import re
import subprocess
import sys
import textwrap

import yaml

HERE = os.path.dirname(os.path.abspath(__file__))
PFX = "DescriptiveComplexity"
CORE = "Lax904597"
CORE_COMMIT = "5aef71b6365249121f68485b77de5e25e26f41bf"
REPOSITORY = "https://github.com/PierreSenellart/descriptive-complexity"
GENERATED = re.compile(r"(_proof_|match_|_simp_|\.rec$|casesOn|noConfusion|\.mk$|\.eq_\d|sizeOf|injEq|"
                       r"\.inj$|\.ext$|ext_iff|brecOn|below|\._f$|\.recOn|binductionOn|ctorIdx)")
KIND = {"fo": "FOReduction", "ordered": "OrderedFOReduction", "relOrdered": "RelOrderedFOReduction"}
LAW = {"fo": "cofinalHard_of_foReduction", "ordered": "cofinalHard_of_orderedReduction",
       "relOrdered": "cofinalHard_of_relOrderedReduction"}


def git_show(library, ref, path):
    r = subprocess.run(["git", "-C", library, "show", f"{ref}:{path}"], capture_output=True, text=True)
    return r.stdout if r.returncode == 0 else None


def git_ls(library, ref, prefix):
    out = subprocess.run(["git", "-C", library, "ls-tree", "-r", "--name-only", ref, prefix],
                         capture_output=True, text=True, check=True).stdout
    return [p for p in out.split("\n") if p.endswith(".lean")]


# ---------------------------------------------------------------- scanning

THEOREM = re.compile(r"^theorem\s+(\w+)\s*(?P<binders>[^:\n]*?):\s*(?P<stmt>[^\n]*?)\s*:=\s*(?P<proof>.*?)"
                     r"(?=\n\n|\n/--|\n(?:theorem|def|end|namespace|section|open|private|noncomputable|@\[)\b)",
                     re.S | re.M)
PROBLEM = re.compile(r"^(?:noncomputable )?def\s+(\w+)\s*:\s*DecisionProblem\s+([\w.]+)\s+where\s*\n"
                     r"\s*Holds\s*:=\s*fun\s+(\w+)\s+(\w+)\s*=>\s*@(\w+)\s+\3\s+\4\s*\n"
                     r"\s*iso_invariant\s*:=\s*fun\s+e\s*=>\s*(\w+)\s+e", re.M)
VOCAB = re.compile(r"^fo_language\s+(\w+)\s+with\s+(\w+)\s+where\s*\n(.*?)(?=\n\S)", re.S | re.M)
MODDOC = re.compile(r"/-!\s*(.*?)-/", re.S)
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)*(?:private |protected |noncomputable )*(?:def|theorem|abbrev|structure|"
                  r"inductive|instance)\s+([\w.]+)", re.M)


def scan(library, ref):
    # the catalog is the library's `Problems/`; the worked examples (graph
    # crawling, conjunctive queries) are submissions of their own
    files = {p: git_show(library, ref, p) for p in git_ls(library, ref, f"{PFX}/Problems")}
    theorems, problems, vocabs, docs, decls = {}, {}, {}, {}, {}
    for path, text in files.items():
        for m in THEOREM.finditer(text):
            theorems[m.group(1)] = {"file": path, "binders": m.group("binders").strip(),
                                    "stmt": m.group("stmt").strip(), "proof": " ".join(m.group("proof").split())}
        for m in PROBLEM.finditer(text):
            problems[m.group(1)] = {"file": path, "lang": m.group(2), "pred": m.group(5), "iso": m.group(6)}
        for m in VOCAB.finditer(text):
            vocabs[m.group(1)] = {"file": path, "pfx": m.group(2),
                                  "symbols": re.findall(r"^\s*(\w+)\s*:\s*(\d+)", m.group(3), re.M)}
        for m in DECL.finditer(text):
            decls.setdefault(m.group(1).rpartition(".")[2], path)
        d = MODDOC.search(text)
        if d:
            docs[path] = d.group(1).strip()
    return theorems, problems, vocabs, docs, decls


def catalog(theorems, problems):
    """The NP-complete problems in the usual shape, keyed by their short
    name, with what their completeness is assembled from."""
    mem_re = re.compile(r"^(\w+)_sigmaSODefinable$")
    mem_red_re = re.compile(r"^NP\.mem_of_foReduction\s+([\w.]+)\s+(\w+)_mem_NP$")
    hard_re = re.compile(r"^NP\.hard_of_(fo|ordered|relOrdered)Reduction\s+([\w.]+)\s+(\w+)_NP_hard$")
    table, skipped = {}, []
    for name, t in theorems.items():
        if not name.endswith("_NP_complete"):
            continue
        key = name[:-len("_NP_complete")]
        if t["binders"] or key in ("SAT", "ntmAccept"):
            skipped.append((key, "parameterized, or in the NP core"))
            continue
        prob = t["stmt"].replace("NP.Complete", "").strip()
        p = problems.get(prob)
        mem, hard = theorems.get(f"{key}_mem_NP"), theorems.get(f"{key}_NP_hard")
        if not (p and mem and hard):
            skipped.append((key, "no bundled problem of the usual shape, or no membership or hardness theorem"))
            continue
        mm, mr, hm = mem_re.match(mem["proof"]), mem_red_re.match(mem["proof"]), hard_re.match(hard["proof"])
        if not ((mm or mr) and hm):
            skipped.append((key, f"membership `{mem['proof'][:40]}` or hardness `{hard['proof'][:50]}` "
                                 "not in the usual shape"))
            continue
        membership = {"sigma": mem["proof"]} if mm else {"reduction": mr.group(1), "source": mr.group(2)}
        table[key] = {"problem": prob, "pred": p["pred"], "iso": p["iso"], "lang": p["lang"], "file": p["file"],
                      "mem": membership, "hard_kind": hm.group(1), "reduction": hm.group(2),
                      "source": hm.group(3)}
    return table, skipped


def family_of(path):
    """The concept module of a definitions file: `Problems/X/Defs.lean` and
    `Problems/X.lean` both give `X`."""
    rel = re.split(r"/(?:Problems|Examples)/", path, 1)[1]
    return rel.split("/")[0].removesuffix(".lean")


# ------------------------------------------------------------- the closure

def predicate_closure(lax_export, library, ref, cache, preds):
    """The library declarations the predicates' meanings rest on: every
    non-generated library constant their proof-term closure reaches, with
    its module. For this library these are all definitions."""
    sys.path.insert(0, lax_export)
    import lax_export as le                       # noqa: E402
    checkout = le.resolve_library(library, ref, PFX, cache)
    lean_path = ":".join(sorted(os.path.join(root, d) for root, dirs, _ in os.walk(os.path.join(checkout, ".lake"))
                                for d in dirs if root.endswith(os.path.join("build", "lib")) and d == "lean"))
    out = os.path.join(cache, "catalog-closure.json")
    subprocess.run(["lean", "--run", os.path.join(lax_export, "Slice.lean"), "closure", PFX, out] + sorted(preds),
                   cwd=checkout, env=dict(os.environ, LEAN_PATH=lean_path), check=True,
                   stdout=subprocess.DEVNULL)
    found = {}
    for e in json.load(open(out, encoding="utf-8"))["constants"]:
        n = e["name"]
        if e["module"].startswith(PFX + ".") and not GENERATED.search(n):
            found[n] = e["module"]
    return found


# ------------------------------------------------------------- generation

def plain_prose(doc):
    """A library module docstring as archive prose: the heading dropped,
    Lean names without their namespace and backticks (the site would set
    backticks as mathematics), reference-style citations reduced to their
    text."""
    body = "\n".join(l for l in doc.split("\n") if not l.startswith("# "))
    # a paragraph pointing at a module of the library is a pointer the
    # archive's reader cannot follow
    body = "\n\n".join(par for par in re.split(r"\n\s*\n", body)
                       if "`" + PFX + ".Problems." not in par and ".lean" not in par)
    body = re.sub(r"`" + PFX + r"\.Problems\.[\w.]+`", lambda m: m.group(0).strip("`").rsplit(".", 1)[1], body)
    body = re.sub(r"`" + PFX + r"\.([\w.]+)`", r"\1", body)
    body = re.sub(r"`FirstOrder\.Language\.(\w+)`", r"\1", body)
    body = re.sub(r"`([^`]+)`", r"\1", body)
    body = re.sub(r"\[([^\]]+)\]\[[^\]]+\]", r"\1", body)
    return body.strip()


def title_of(doc, fallback):
    m = re.match(r"#\s*(.+)", doc or "")
    if not m:
        return fallback
    return re.sub(r"\s*:\s*definitions?\s*$", "", m.group(1)).strip()


def write(path, text):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8") as fh:
        fh.write(text)


def module_name(path):
    return path.replace("/", ".").removesuffix(".lean")


PROBLEMS_MODULE = '''import {core}.Problems

/-!
---
title: Problems given by a property of structures
type: definition
---
The decision problems of the NP core are bundled with a proof that they do
not distinguish isomorphic structures. For the problems of this catalog the
bundling is done once and for all: the problem given by a property $P$ of
structures has as yes-instances the structures isomorphic to one satisfying
$P$, which is invariant by construction. When $P$ is itself invariant, as
every property of the catalog is, this is the problem whose yes-instances are
exactly the structures satisfying $P$; that equivalence is stated, problem by
problem, next to each definition.
-/

namespace {cname}.Problems

open FirstOrder FirstOrder.Language {core}.Problems

/-- The decision problem whose yes-instances are the structures isomorphic to
one satisfying `P`. -/
def DecisionProblem.ofPred {{L : Language.{{0, 0}}}} [L.IsRelational]
    (P : ∀ (A : Type) [L.Structure A], Prop) : DecisionProblem L where
  Holds := fun A _ => ∃ (B : Type) (i : L.Structure B) (_ : @Language.Equiv L B A i _), @P B i
  iso_invariant := fun e =>
    ⟨fun ⟨B, i, f, h⟩ => ⟨B, i, e.comp f, h⟩, fun ⟨B, i, f, h⟩ => ⟨B, i, e.symm.comp f, h⟩⟩

end {cname}.Problems
'''

COMMON_BRIDGE = '''import {core}.Interpretations
import {core}.Relativized
import {cname}.Problems

/-!
# Transport along agreements, and the problems given by a property

The library bundles each problem with its own invariance proof; the catalog
bundles a problem as the structures isomorphic to one with the property. The
two agree on every structure once the property is invariant, and a reduction
transports along such agreements at both ends.
-/

namespace {pname}.Common

open FirstOrder FirstOrder.Language
open {core}.Problems {core}.Interpretations {core}.Relativized {cname}.Problems

/-- For an invariant property, the problem it gives holds exactly where the
property does. -/
theorem ofPred_iff {{L : Language.{{0, 0}}}} [L.IsRelational] {{P : ∀ (A : Type) [L.Structure A], Prop}}
    (hP : ∀ {{A B : Type}} [L.Structure A] [L.Structure B], (A ≃[L] B) → (P A ↔ P B))
    (V : Type) [L.Structure V] : DecisionProblem.ofPred P V ↔ P V := by
  constructor
  · rintro ⟨B, i, f, h⟩
    exact (hP f).mp h
  · intro h
    exact ⟨V, inferInstance, Language.Equiv.refl _ _, h⟩

/-- A first-order reduction transported along agreements of its two ends. -/
def FOReduction.congr {{L L' : Language.{{0, 0}}}} [L.IsRelational] [L'.IsRelational]
    {{P P' : DecisionProblem L}} {{Q Q' : DecisionProblem L'}}
    (hP : ∀ (A : Type) [L.Structure A], P A ↔ P' A) (hQ : ∀ (A : Type) [L'.Structure A], Q A ↔ Q' A)
    (f : FOReduction P Q) : FOReduction P' Q' :=
  letI := f.tagFinite
  letI := f.tagNonempty
  {{ Tag := f.Tag
    dim := f.dim
    toInterpretation := f.toInterpretation
    correct := fun A _ _ _ => ((hP A).symm.trans (f.correct A)).trans (hQ _) }}

/-- An ordered first-order reduction transported along agreements of its two
ends. -/
def OrderedFOReduction.congr {{L L' : Language.{{0, 0}}}} [L.IsRelational] [L'.IsRelational]
    {{P P' : DecisionProblem L}} {{Q Q' : DecisionProblem L'}}
    (hP : ∀ (A : Type) [L.Structure A], P A ↔ P' A) (hQ : ∀ (A : Type) [L'.Structure A], Q A ↔ Q' A)
    (f : OrderedFOReduction P Q) : OrderedFOReduction P' Q' :=
  letI := f.tagFinite
  letI := f.tagNonempty
  {{ Tag := f.Tag
    dim := f.dim
    toInterpretation := f.toInterpretation
    correct := fun A _ _ _ _ => ((hP A).symm.trans (f.correct A)).trans (hQ _) }}

/-- A relativized ordered first-order reduction transported along agreements
of its two ends. -/
def RelOrderedFOReduction.congr {{L L' : Language.{{0, 0}}}} [L.IsRelational] [L'.IsRelational]
    {{P P' : DecisionProblem L}} {{Q Q' : DecisionProblem L'}}
    (hP : ∀ (A : Type) [L.Structure A], P A ↔ P' A) (hQ : ∀ (A : Type) [L'.Structure A], Q A ↔ Q' A)
    (f : RelOrderedFOReduction P Q) : RelOrderedFOReduction P' Q' :=
  letI := f.tagFinite
  {{ Tag := f.Tag
    dim := f.dim
    toRelInterpretation := f.toRelInterpretation
    dom_nonempty := f.dom_nonempty
    correct := fun A _ _ _ _ => ((hP A).symm.trans (f.correct A)).trans (hQ _) }}

end {pname}.Common
'''


# The one parameterized problem of the catalog, k-colorability, NP-complete
# for every k ≥ 3: written out, since its statements carry the parameter.
KCOL_CONCEPT = '''/-- The property `KColorable k` is isomorphism-invariant, for every `k`. -/
axiom kColorable_iso : ∀ {k : ℕ} {A B : Type} [FirstOrder.Language.graph.Structure A]
  [FirstOrder.Language.graph.Structure B],
  (A ≃[FirstOrder.Language.graph] B) → (KColorable k A ↔ KColorable k B)

/-- The problem KCol k: is the graph k-colorable? -/
def KCol (k : ℕ) : DecisionProblem FirstOrder.Language.graph :=
  DecisionProblem.ofPred (KColorable k)

/-- The yes-instances of KCol k are exactly the k-colorable graphs. -/
axiom kCol_iff : ∀ (k : ℕ) (A : Type) [FirstOrder.Language.graph.Structure A],
  KCol k A ↔ KColorable k A

/-- k-colorability is NP-complete for every k ≥ 3. -/
axiom kCol_NP_complete : ∀ {k : ℕ}, 3 ≤ k → NP.Complete (KCol k)'''

KCOL_BRIDGE = '''/--
---
conclusion: {cname}.Coloring.kColorable_iso
---
The library's invariance theorem for KColorable.
-/
theorem kColorable_iso {{k : ℕ}} {{A B : Type}} [FirstOrder.Language.graph.Structure A]
    [FirstOrder.Language.graph.Structure B] (e : A ≃[FirstOrder.Language.graph] B) :
    KColorable k A ↔ KColorable k B :=
  {pfx}.kColorable_iso e

/--
---
conclusion: {cname}.Coloring.kCol_iff
---
The problem given by an invariant property holds exactly where the property
does.
-/
theorem kCol_iff (k : ℕ) (A : Type) [FirstOrder.Language.graph.Structure A] :
    KCol k A ↔ KColorable k A :=
  Common.ofPred_iff (fun e => {pfx}.kColorable_iso e) A

/-- The library's bundled `KCol k` and the catalog's agree on every structure. -/
theorem kCol_agree (k : ℕ) (A : Type) [FirstOrder.Language.graph.Structure A] :
    {pfx}.KCol k A ↔ KCol k A :=
  (kCol_iff k A).symm

/--
---
conclusion: {cname}.Coloring.kCol_NP_complete
---
Membership from the library's existential second-order definition of
$k$-colorability; hardness by padding the reduction of 3-colorability to
$k$-colorability with $k - 3$ further colors, 3-colorability being NP-hard by
the catalog's statement for it.
-/
theorem kCol_NP_complete {{k : ℕ}} (hk : 3 ≤ k) : NP.Complete (KCol k) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = 3 + m := ⟨k - 3, by omega⟩
  exact ⟨({core}.NPClass.NP_mem_congr_finite fun A _ _ => kCol_agree (3 + m) A).mp
      ({pfx}.kCol_sigmaSODefinable (3 + m)),
    {core}.NPClass.cofinalHard_of_foReduction
      (Common.FOReduction.congr {pname}.Bridge.ThreeColorability.threeCol_agree (kCol_agree (3 + m))
        ({pfx}.threeCol_fo_reduction_kCol m))
      {cname}.ThreeColorability.threeCol_NP_complete.2⟩'''


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--out", required=True, help="the submission folder `lax init` made")
    ap.add_argument("--library", default=os.path.dirname(HERE), help="the library checkout (default: this one)")
    ap.add_argument("--ref", default="v1.2.2")
    ap.add_argument("--lax-export", default=os.path.expanduser("~/git/software/lax-export"))
    ap.add_argument("--core", default=os.path.join(HERE, "np-core"), help="the registered NP core's folder")
    ap.add_argument("--cache", default=os.environ.get("LAX_EXPORT_CACHE") or
                    os.path.join(os.environ.get("TMPDIR") or os.environ.get("TEMP") or os.environ.get("TMP") or "/tmp",
                                 "lax-export"))
    ap.add_argument("--only", help="comma-separated problem keys to include (default: all)")
    args = ap.parse_args()
    out = os.path.abspath(args.out)
    manifest = yaml.safe_load(open(os.path.join(out, "manifest.yaml"), encoding="utf-8"))
    cname = "Lax" + manifest["id"].split("-")[1]
    pname = cname + "Proofs"
    overrides = {}
    if os.path.isfile(os.path.join(out, "catalog.yaml")):
        overrides = yaml.safe_load(open(os.path.join(out, "catalog.yaml"), encoding="utf-8")) or {}

    theorems, problems, vocabs, docs, decls = scan(args.library, args.ref)
    table, skipped = catalog(theorems, problems)
    if args.only:
        keep = set(args.only.split(","))
        table = {k: v for k, v in table.items() if k in keep}
    for key, why in sorted(skipped):
        print(f"skipped {key}: {why}", file=sys.stderr)
    for key, p in table.items():
        for src in (p["source"], p["mem"].get("source", "sat")):
            if src != "sat" and src not in table:
                sys.exit(f"{key} reduces from or to {src}, which is not in the catalog")
    # problems in dependency order (a problem after the ones its membership
    # and hardness come from), then grouped by family in that order
    order, seen = [], set()
    def visit(k):
        if k in seen or k == "sat":
            return
        seen.add(k)
        visit(table[k]["source"])
        visit(table[k]["mem"].get("source", "sat"))
        order.append(k)
    for k in sorted(table):
        visit(k)
    families = {}                                   # family -> [problem keys]
    for key in order:
        families.setdefault(family_of(table[key]["file"]), []).append(key)
    families = dict(sorted(families.items(), key=lambda kv: min(order.index(k) for k in kv[1])))
    print(f"{len(table)} problems in {len(families)} families", file=sys.stderr)

    # the definitions the concepts restate: the predicates' closure, each in
    # the module of its family (a vocabulary in the family declaring it)
    preds = {f"{PFX}.{p['pred']}" for p in table.values()}
    with_kcol = "Coloring" in {family_of(p["file"]) for p in table.values()} and "threeCol" in table
    if with_kcol:
        preds.add(f"{PFX}.KColorable")
    found = predicate_closure(args.lax_export, args.library, args.ref, args.cache, preds)
    core_cfg = yaml.safe_load(open(os.path.join(args.core, "export.yaml"), encoding="utf-8"))
    core_map = {k: f"{CORE}.{v}" for k, v in core_cfg.get("restated", {}).items()}
    restated = {}
    def core_has(n):
        """The core restates `n`, or the declaration `n` is generated by (a
        constructor, a field) and so goes with it."""
        parts = n.split(".")
        return any(".".join(parts[:i]) in core_map for i in range(1, len(parts) + 1))
    for n, mod in sorted(found.items()):
        if core_has(n):
            continue
        path = mod.replace(".", "/") + ".lean"
        fam = family_of(path) if re.search(r"/(Problems|Examples)/", path) else "Common"
        short = n.split(".", 2)[2] if n.startswith("FirstOrder.Language.") else n[len(PFX) + 1:]
        restated[n] = f"{fam}.{short}"
    for v, info in vocabs.items():                 # a vocabulary's generated instances
        if f"FirstOrder.Language.{v}" in restated:
            fam = family_of(info["file"])
            cap = v[0].upper() + v[1:]
            for n in (f"FirstOrder.Language.instIsRelational{cap}", f"FirstOrder.Language.instDecidableEq{cap}Rel"):
                restated.setdefault(n, f"{fam}.{n.rpartition('.')[2]}")

    def lang_ref(lang):
        """How a problem's vocabulary is written: the catalog's restatement,
        the core's, or Mathlib's."""
        full = "FirstOrder." + lang
        if full in restated:
            return f"{cname}.{restated[full]}"
        if full in core_map:
            return core_map[full]
        return full

    # the export file
    targets = sorted({f"{PFX}.{p[k]}" for p in table.values() for k in ("iso", "reduction")}
                     | {f"{PFX}.{p['mem'].get('sigma') or p['mem']['reduction']}" for p in table.values()}
                     | ({f"{PFX}.kColorable_iso", f"{PFX}.kCol_sigmaSODefinable", f"{PFX}.threeCol_fo_reduction_kCol"}
                        if with_kcol else set()))
    export = {
        "library": REPOSITORY, "ref": args.ref, "prefix": PFX, "targets": targets,
        "copyright": "2026 Pierre Senellart",
        "manifest": {k: manifest[k] for k in ("title", "authors", "bibEntries") if k in manifest},
        "requires": [{"package": CORE, "repository": REPOSITORY, "commit": CORE_COMMIT, "folder": "lax/np-core",
                      "restated_from": os.path.relpath(os.path.join(args.core, "export.yaml"), out)}],
        "restated": restated,
    }
    with open(os.path.join(out, "export.yaml"), "w", encoding="utf-8") as fh:
        fh.write(f"# Generated by lax/catalog.py from the library at {args.ref}; do not edit.\n")
        yaml.safe_dump(export, fh, sort_keys=False, allow_unicode=True, width=1000)

    # the skeletons of the restated definitions, from lax-export
    r = subprocess.run([sys.executable, os.path.join(args.lax_export, "lax_export.py"), "export.yaml", "--skeleton",
                        "--cache", args.cache], cwd=out, capture_output=True, text=True)
    sys.stderr.write(r.stderr)
    sys.stderr.write("".join(l + "\n" for l in r.stdout.splitlines() if l.startswith("skeleton note")))
    if r.returncode:
        sys.exit("lax-export failed")
    skel_dir = os.path.join(out, "skeleton", cname)

    # the concept modules: the skeleton's restatements, then per problem the
    # bundled problem and its three claims
    cdir = os.path.join(out, "concepts", cname)
    write(os.path.join(cdir, "Problems.lean"), PROBLEMS_MODULE.format(core=CORE, cname=cname))
    skeleton_only = {f[:-5] for f in os.listdir(skel_dir)} - set(families) if os.path.isdir(skel_dir) else set()
    for fam in sorted(set(families) | skeleton_only):
        keys = families.get(fam, [])
        skel_path = os.path.join(skel_dir, fam + ".lean")
        skel = open(skel_path, encoding="utf-8").read() if os.path.isfile(skel_path) else None
        doc = docs.get(table[keys[0]]["file"], "") if keys else ""
        title = overrides.get(fam, {}).get("title") or title_of(doc, fam)
        prose = overrides.get(fam, {}).get("description") or plain_prose(doc) or \
            "Definitions the catalog's problems rest on, restated from the library."
        if skel:
            head, _, rest = skel.partition("/-!")
            _, _, rest = rest.partition("-/")
            body = rest.rstrip()
            assert body.endswith(f"end {cname}.{fam}"), fam
            body = body[:-len(f"end {cname}.{fam}")].rstrip()
            imports = [l for l in head.split("\n") if l.startswith("import ")]
        else:
            body, imports = f"namespace {cname}.{fam}", []
        for extra in (f"import {CORE}.Classes", f"import {cname}.Problems"):
            if extra not in imports:
                imports.append(extra)
        parts = [f"open {CORE}.Problems {CORE}.Classes {cname}.Problems"] if keys else []
        for key in keys:
            p = table[key]
            P, pred, L = p["problem"], p["pred"], lang_ref(p["lang"])
            iff_doc = textwrap.fill(f"/-- The yes-instances of {P} are exactly the structures satisfying "
                                    f"`{pred}`. -/", 78)
            parts.append(f'''/-- The property `{pred}` is isomorphism-invariant. -/
axiom {p["iso"]} : ∀ {{A B : Type}} [{L}.Structure A] [{L}.Structure B],
  (A ≃[{L}] B) → ({pred} A ↔ {pred} B)

/-- The problem {P}: does the structure satisfy `{pred}`? -/
def {P} : DecisionProblem {L} :=
  DecisionProblem.ofPred {pred}

{iff_doc}
axiom {key}_iff : ∀ (A : Type) [{L}.Structure A], {P} A ↔ {pred} A

/-- {P} is NP-complete. -/
axiom {key}_NP_complete : NP.Complete {P}''')
        if fam == "Coloring" and with_kcol:
            parts.append(KCOL_CONCEPT)
        kind = "theorem" if keys else "definition"
        body = body.lstrip("\n")
        text = "\n".join(imports) + f"\n\n/-!\n---\ntitle: {title}\ntype: {kind}\n---\n{prose}\n-/\n\n" + body + \
            ("\n\n" + "\n\n".join(parts) if parts else "") + f"\n\nend {cname}.{fam}\n"
        write(os.path.join(cdir, fam + ".lean"), text)

    # the bridges: per family, the invariance theorem, the agreement, and
    # completeness assembled from the core's statements
    bdir = os.path.join(out, "proofs", pname, "Bridge")
    write(os.path.join(bdir, "Common.lean"), COMMON_BRIDGE.format(core=CORE, cname=cname, pname=pname))
    for fam, keys in families.items():
        imports = [f"import {CORE}.CookLevin", f"import {CORE}.NPClass", f"import {cname}.{fam}",
                   f"import {pname}.Bridge.Common"]
        for key in keys:
            p = table[key]
            mem_decl = p["mem"].get("sigma") or p["mem"]["reduction"].rpartition(".")[2]
            for name in (p["iso"], mem_decl, p["reduction"].rpartition(".")[2]):
                path = decls.get(name)
                if not path:
                    sys.exit(f"{key}: cannot find the module declaring {name}")
                imports.append(f"import {pname}.{module_name(path)}")
            for src in (p["source"], p["mem"].get("source", "sat")):
                if src != "sat" and family_of(table[src]["file"]) != fam:
                    imports.append(f"import {pname}.Bridge.{family_of(table[src]['file'])}")
        imports = list(dict.fromkeys(imports))
        parts = []
        for key in keys:
            p = table[key]
            P, pred, L, src = p["problem"], p["pred"], lang_ref(p["lang"]), p["source"]
            def agree_and_statement(q):
                if q == "sat":
                    return "(fun _ _ => Iff.rfl)", f"{CORE}.CookLevin.SAT_NP_complete"
                qfam = family_of(table[q]["file"])
                return f"{pname}.Bridge.{qfam}.{q}_agree", f"{cname}.{qfam}.{q}_NP_complete"
            src_agree, src_stmt = agree_and_statement(src)
            src_hard = src_stmt + ".2"
            if "sigma" in p["mem"]:
                mem_proof = (f"({CORE}.NPClass.NP_mem_congr_finite fun A _ _ => {key}_agree A).mp "
                             f"{PFX}.{p['mem']['sigma']}")
                mem_prose = f"Membership from the library's existential second-order definition of {P}"
            else:
                tgt = p["mem"]["source"]
                tgt_agree, tgt_stmt = agree_and_statement(tgt)
                mem_proof = (f"{CORE}.NPClass.NP_mem_of_foReduction\n      "
                             f"(Common.FOReduction.congr {key}_agree {tgt_agree} {PFX}.{p['mem']['reduction']}) "
                             f"{tgt_stmt}.1")
                mem_prose = (f"Membership from the library's reduction of {P} to "
                             f"{table[tgt]['problem'] if tgt != 'sat' else 'SAT'}, which is in NP")
            complete_prose = textwrap.fill(
                f"{mem_prose}; hardness from the library's reduction out of "
                f"{table[src]['problem'] if src != 'sat' else 'SAT'}, which is NP-hard by the "
                f"{'NP core’s Cook–Levin theorem' if src == 'sat' else 'catalog’s statement for it'}. "
                f"Both are transported to the catalog's problems along the agreements.", 78)
            parts.append(f'''/--
---
conclusion: {cname}.{fam}.{p["iso"]}
---
The library's invariance theorem for {pred}.
-/
theorem {p["iso"]} {{A B : Type}} [{L}.Structure A] [{L}.Structure B] (e : A ≃[{L}] B) :
    {pred} A ↔ {pred} B :=
  {PFX}.{p["iso"]} e

/--
---
conclusion: {cname}.{fam}.{key}_iff
---
The problem given by an invariant property holds exactly where the property
does.
-/
theorem {key}_iff (A : Type) [{L}.Structure A] : {P} A ↔ {pred} A :=
  Common.ofPred_iff @{PFX}.{p["iso"]} A

/-- The library's bundled {P} and the catalog's agree on every structure. -/
theorem {key}_agree (A : Type) [{L}.Structure A] : {PFX}.{P} A ↔ {P} A :=
  ({key}_iff A).symm

/--
---
conclusion: {cname}.{fam}.{key}_NP_complete
---
{complete_prose}
-/
theorem {key}_NP_complete : NP.Complete {P} :=
  ⟨{mem_proof},
    {CORE}.NPClass.{LAW[p["hard_kind"]]}
      (Common.{KIND[p["hard_kind"]]}.congr {src_agree} {key}_agree {PFX}.{p["reduction"]}) {src_hard}⟩''')
        if fam == "Coloring" and with_kcol:
            for name in ("kCol_sigmaSODefinable", "threeCol_fo_reduction_kCol"):
                imports.append(f"import {pname}.{module_name(decls[name])}")
            imports.append(f"import {pname}.Bridge.ThreeColorability")
            imports = list(dict.fromkeys(imports))
            parts.append(KCOL_BRIDGE.format(cname=cname, pname=pname, core=CORE, pfx=PFX))
        text = "\n".join(imports) + f"\n\nnamespace {pname}.Bridge.{fam}\n\n" + \
            f"open FirstOrder FirstOrder.Language\nopen {CORE}.Problems {CORE}.Interpretations " + \
            f"{CORE}.Relativized {CORE}.Classes {cname}.Problems {cname}.{fam}\n\n" + \
            "\n\n".join(parts) + f"\n\nend {pname}.Bridge.{fam}\n"
        write(os.path.join(bdir, fam + ".lean"), text)
    # the export again, so that the root modules list the generated files
    r = subprocess.run([sys.executable, os.path.join(args.lax_export, "lax_export.py"), "export.yaml",
                        "--cache", args.cache], cwd=out, capture_output=True, text=True)
    sys.stderr.write(r.stderr.splitlines()[-1] + "\n" if r.stderr.strip() else "")
    if r.returncode:
        sys.exit("lax-export failed")
    print(f"written: {len(families)} concept modules and bridges for {len(table)} problems", file=sys.stderr)


if __name__ == "__main__":
    main()
