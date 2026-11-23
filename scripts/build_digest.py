#!/usr/bin/env python3
"""Build a deformalization digest: one cluster of the Lean archive rewritten as ordinary mathematics.

    python3 -B scripts/build_digest.py [SLUG ...]  # data.tex and figure, LuaLaTeX, checks (all digests if none named)
    python3 -B scripts/build_digest.py --refresh  # first re-read the Lean archive (needs its source)
    python3 -B scripts/build_digest.py --check    # only verify the stored records
    python3 -B scripts/build_digest.py --edition  # build, and keep the PDF as a published edition (editions/)

The first digest is digests/tower-bound/ ("Twisted cokernels in a cyclotomic tower"). Its text,
tower-bound.tex, is hand-written, and its declarations, examples and outline are listed in this file.
Every later digest digests/<slug>/ has a file spec.py with DIRECTORY, DECLS, OUTLINE and, optionally,
QUOTED, LETTERED and ELSEWHERE (for a note that treats one part of its unit: the subjects of the other
members, by source file). Everything in a note that is a Lean name, a line range, a count or a
number of an example is generated here:

* concordance.json  the declarations of the cluster with their pinned line ranges, the SHA-256 of
                    each source file and the statement as written in the archive (a quotation).
                    It is written by --refresh from the archive source and is afterwards the
                    record the public tree builds from; without --refresh the script compares it
                    with the archive whenever the archive is present.
* atlas-cluster.json where the embedding atlas places each declaration (--refresh-atlas, network).
* data.tex          macros: linked Lean names, counts, the numbers of the two examples.
* figure.tex        the picture of the first example, drawn from the computed values.

The examples are computed in exact rational arithmetic and every displayed value is asserted
against the closed formula proved in the text. The build fails on an overfull box, a very loose
line, a missing glyph, an undefined reference, or a letter used in a formula that the notation
list does not mention.
"""
from __future__ import annotations

import collections
import hashlib
import json
import os
import re
import runpy
import shutil
import subprocess
import sys
from fractions import Fraction as Fr
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from build_guide import check_notation, tex_escape, url_escape  # noqa: E402

FIRST = "tower-bound"   # the first digest: its declarations, examples and outline are in this file
DIGEST = FIRST
D = ROOT / "digests" / DIGEST
ATLAS = EXAMPLES = True  # the first digest starts from a cluster of the embedding atlas and has computed examples
ELSEWHERE: list = []     # (id, title, [source file names]): members of the unit that other notes will treat
PAGES = None        # fixed after the first build (so that a change of length is noticed)
ATLAS_SITE = "https://nasqret.github.io/riemann-proof-atlas/"
ATLAS_RAW = "https://raw.githubusercontent.com/nasqret/riemann-proof-atlas/"
BUNDLE = "iwasawa-7c448cddb3"       # the cluster of the embedding atlas this digest starts from

AV = "Development/AutomorphicArithmetic/AutomorphicVarieties/"
A = AV + "AdditiveValuationNorms/"
LI = AV + "LayeredIsomorphisms/"
NT = AV + "NumberFieldTowers/"
GL = AV + "GaloisLibrary/"
TR = "Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/TotallyRealRoots/"

# key, name shown, file, word that opens the declaration, name as written at its head
DECLS = [
    # definitions
    ("GenBy", "GenBy", A + "CokLenLeOfRangeLe.lean", "def", "GenBy"),
    ("jZero", "jZero", A + "CokLenLeOfRangeLe.lean", "abbrev", "jZero"),
    ("IsLevel", "IsLevel", A + "CokLenLeOfRangeLe.lean", "def", "IsLevel"),
    ("cokLen", "cokLen", A + "CokLenLeOfRangeLe.lean", "def", "cokLen"),
    ("InPow", "InPow", A + "CokLenLeOfRangeLe.lean", "def", "InPow"),
    ("Unip", "Unip", A + "CokLenLeOfRangeLe.lean", "def", "Unip"),
    ("twLen", "twLen", A + "CokLenLeOfRangeLe.lean", "def", "twLen"),
    # lengths and determinants
    ("range", "cokLen_le_of_range_le", A + "CokLenLeOfRangeLe.lean", "theorem", "cokLen_le_of_range_le"),
    ("lenComp", "Base.lenComp", GL + "SelmerTransport/LenComp.lean", "theorem", "UpperTheory.V.Base.lenComp"),
    ("smith", "length_cokernel_eq_addVal_det",
     "Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/SelmerDuality/LengthDet.lean",
     "theorem", "length_cokernel_eq_addVal_det"),
    ("lift", "lift", A + "ImportsAlt.lean", "theorem", "UpperTheory.V.PropA.lift"),
    # centres
    ("lte", "abelian₂.lte", GL + "LocalRingsCompletion/IsUnitAddMem.lean", "theorem", "UpperTheory.V.abelian₂.lte"),
    ("lteNorm", "lteNorm", A + "LteNorm.lean", "theorem", "UpperTheory.V.PropA.lteNorm"),
    ("units", "padic_units_distance_le_max", A + "PadicUnitsDistanceLeMax.lean", "private theorem",
     "padic_units_distance_le_max"),
    ("helly", "helly", A + "Helly.lean", "theorem", "UpperTheory.V.PropA.helly"),
    ("ball", "ball", A + "PadicUnitsDistanceLeMax.lean", "theorem", "UpperTheory.V.PropA.ball"),
    ("detFactor", "detFactor", A + "DetFactor.lean", "theorem", "UpperTheory.V.PropA.detFactor"),
    ("normVal", "normVal", A + "NormVal.lean", "theorem", "UpperTheory.V.PropA.normVal"),
    ("detBound", "detBound", A + "DetBound.lean", "theorem", "UpperTheory.V.PropA.detBound"),
    ("level", "exists_centres_level", A + "ExistsCentresLevel.lean", "theorem", "exists_centres_level"),
    # growth
    ("cokL", "cokL", A + "CokLen.lean", "theorem", "UpperTheory.V.PropA.cokL"),
    ("nilLen", "nilLen", A + "NilLen.lean", "theorem", "UpperTheory.V.PropA.nilLen"),
    ("unipPow", "unipPow", A + "UnipPow.lean", "theorem", "UpperTheory.V.PropA.unipPow"),
    ("frob", "frob", A + "Imports.lean", "theorem", "UpperTheory.V.PropA.frob"),
    ("powIn", "powIn", A + "PowIn.lean", "theorem", "UpperTheory.V.PropA.powIn"),
    ("phi", "phi", A + "ImportsTer.lean", "theorem", "UpperTheory.V.PropA.phi"),
    ("step", "step", A + "ImportsMore.lean", "theorem", "UpperTheory.V.PropA.step"),
    ("mono", "mono", A + "ImportsBis.lean", "theorem", "UpperTheory.V.PropA.mono"),
    ("twist", "twist", A + "ImportsFurther.lean", "theorem", "UpperTheory.V.PropA.twist"),
    ("growth", "growth", A + "Growth.lean", "theorem", "UpperTheory.V.PropA.growth"),
    ("twgrowth", "twLen_le_growth", A + "ExistsCentresLevel.lean", "theorem", "twLen_le_growth"),
    ("centres", "exists_centres", A + "ExistsCentresLevel.lean", "theorem", "exists_centres"),
    # exceptional twists
    ("centresnorm", "exists_centres_norm", A + "ExistsCentresLevel.lean", "theorem", "exists_centres_norm"),
    ("near1", "Win.near1", LI + "Near1.lean", "theorem", "UpperTheory.V.Win.near1"),
    ("exc", "Win.exc", LI + "Exc.lean", "theorem", "UpperTheory.V.Win.exc"),
    # duality
    ("qzInj", "qzInj", A + "QzInj.lean", "theorem", "UpperTheory.V.PropA.qzInj"),
    ("dualDiv", "dualDiv", A + "DualDiv.lean", "theorem", "UpperTheory.V.PropA.dualDiv"),
    ("torsFin", "torsFin", A + "TorsFin.lean", "theorem", "UpperTheory.V.PropA.torsFin"),
    ("dualUnip", "dualUnip", A + "DualUnip.lean", "theorem", "UpperTheory.V.PropA.dualUnip"),
    # arithmetic
    ("XDual", "XDual", GL + "KummerTheory/Mk0IdMapCongr.lean", "def", "XDual"),
    ("IsTower", "Tower.IsTower", NT + "XTwApplyApply.lean", "structure", "IsTower"),
    ("IsLayer", "IsLayer", AV + "StmtFields.lean", "def", "IsLayer"),
    ("shaInv", "shaInv", GL + "GaloisCohomologyLength/LevelInertiaLeLevelDec.lean", "def", "shaInv"),
    ("VLen", "VLen", "Formalism/GaloisCohomology/Statement.lean", "def", "VLen"),
    ("ABound", "Win.ABound", LI + "SecondBound.lean", "def", "ABound"),
    ("SecondBound", "Win.SecondBound", LI + "SecondBound.lean", "def", "SecondBound"),
    ("FirstBound", "Win.FirstBound", LI + "SecondBound.lean", "def", "FirstBound"),
    ("dinfNil", "Kum.dinfNil", GL + "KummerTheory/DinfNil.lean", "theorem", "UpperTheory.V.Kum.dinfNil"),
    ("xUnip", "xUnip", A + "XUnip.lean", "theorem", "UpperTheory.V.PropA.xUnip"),
    ("step0", "Tower.step0", NT + "ExistsDescends.lean", "theorem", "step0"),
    ("isTowerIff", "Tower.isTower_iff", NT + "ExistsDescends.lean", "theorem", "isTower_iff"),
    ("Descends", "Descends", A + "ABoundOfDescends.lean", "def", "Descends"),
    ("descends", "descends", A + "Descends.lean", "theorem", "UpperTheory.V.PropA.descends"),
    ("cycRange", "Tower.cycRange", NT + "CycRange.lean", "theorem", "UpperTheory.V.Tower.cycRange"),
    ("genLevel", "genLevel", A + "GenLevel.lean", "theorem", "UpperTheory.V.PropA.genLevel"),
    ("shaLeV", "shaLeV", A + "ShaLeV.lean", "theorem", "UpperTheory.V.PropA.shaLeV"),
    ("aDesc", "aBound_of_descends", A + "ABoundOfDescends.lean", "theorem", "aBound_of_descends"),
    ("aTower", "aBound_of_isTower", A + "ABoundOfIsTower.lean", "theorem", "UpperTheory.V.PropA.aBound_of_isTower"),
    # the window
    ("FW", "Published.FerreroWashington", AV + "PublishedTheorems/FerreroWashington.lean", "def", "FerreroWashington"),
    ("FWthm", "FW.ferreroWashington", GL + "FerreroWashingtonIndex/FerreroWashington.lean", "theorem",
     "UpperTheory.V.FW.ferreroWashington"),
    ("towerFixed", "Two.towerFixed", AV + "QuadraticExtensions/IsAlgClosureRat.lean", "theorem", "towerFixed"),
    ("fixedIn", "Two.fixedIn", AV + "QuadraticExtensions/IsAlgClosureRat.lean", "theorem", "fixedIn"),
    ("twoIn", "Two.twoIn", AV + "QuadraticExtensions/IsAlgClosureRat.lean", "theorem", "twoIn"),
    ("LemmaK", "LemmaK", AV + "GeneratorCountTuples/LemmaK.lean", "def", "LemmaK"),
    ("window", "Win.window", LI + "Window.lean", "theorem", "UpperTheory.V.Win.window"),
    ("thmBab", "Win.thmBab_of", LI + "ThmBabOf.lean", "theorem", "UpperTheory.V.Win.thmBab_of"),
    ("thmBabK", "Win.thmBab_of_lemmaK", LI + "ThmBabOfLemmaK.lean", "theorem", "thmBab_of_lemmaK"),
    # the valuation, and the auxiliary lemmas of proofs given in the text
    ("vl", "vl", A + "CokLenLeOfRangeLe.lean", "abbrev", "vl"),
    ("normDvd", "norm_le_of_dvd'", A + "LteNorm.lean", "private theorem", "norm_le_of_dvd'"),
    ("normAddVal", "norm_eq_of_addVal", A + "LteNorm.lean", "private theorem", "norm_eq_of_addVal"),
    ("dvdNorm", "dvd_of_norm_le'", A + "NormVal.lean", "private theorem", "dvd_of_norm_le'"),
    ("vlProd", "vl_prod", A + "NormVal.lean", "private theorem", "vl_prod"),
    ("nilSucc", "nilLen_range_succ", A + "NilLen.lean", "private theorem", "nilLen_range_succ"),
    ("nilLt", "nilLen_lt", A + "NilLen.lean", "private theorem", "nilLen_lt"),
    ("vlNorm", "vl_le_of_norm", A + "ExistsCentresLevel.lean", "theorem", "vl_le_of_norm"),
    ("memLev", "mem_levU_one", A + "ABoundOfDescends.lean", "theorem", "mem_levU_one"),
    ("eqTwLen", "Descends.eq_twLen", A + "ABoundOfDescends.lean", "theorem", "Descends.eq_twLen"),
    # descent to a layer: characters and lengths
    ("qzSep", "Tower.qzSep", NT + "QzSep.lean", "theorem", "UpperTheory.V.Tower.qzSep"),
    ("qzAnn", "exists_qz_ne_zero_annihilators_of_ne_zero", NT + "QzSep.lean", "private theorem",
     "exists_qz_ne_zero_annihilators_of_ne_zero"),
    ("exactDual", "exact_dual", NT + "LenDual.lean", "private theorem", "exact_dual"),
    ("simpleDual", "simple_dual", NT + "LenDual.lean", "private theorem", "simple_dual"),
    ("leDual", "le_dual", NT + "LenDual.lean", "private theorem", "le_dual"),
    ("lenDual", "Tower.lenDual", NT + "LenDual.lean", "theorem", "UpperTheory.V.Tower.lenDual"),
    ("dualKer", "Tower.dualKer", NT + "DualKer.lean", "theorem", "UpperTheory.V.Tower.dualKer"),
    ("cokerDual", "Tower.cokerDual", NT + "CokerDual.lean", "theorem", "UpperTheory.V.Tower.cokerDual"),
    # descent to a layer: principal units and layers
    ("pgIndex", "pg_index", NT + "PrincGen.lean", "private theorem", "pg_index"),
    ("pgExists", "pg_exists", NT + "PrincGen.lean", "private theorem", "pg_exists"),
    ("pgEmult", "pg_emult", NT + "PrincGen.lean", "private theorem", "pg_emult"),
    ("princGen", "Tower.princGen", NT + "PrincGen.lean", "theorem", "UpperTheory.V.Tower.princGen"),
    ("princClosed", "princ_le_of_isClosed", TR + "Generate.lean", "theorem", "princ_le_of_isClosed"),
    ("lteOdd", "emultiplicity_pow_sub_one_odd", TR + "EmultiplicityPowSubOneOdd.lean", "theorem",
     "emultiplicity_pow_sub_one_odd"),
    ("lteSq", "emultiplicity_pow_sub_one_sq", TR + "EmultiplicityPowSubOneOdd.lean", "theorem",
     "emultiplicity_pow_sub_one_sq"),
    ("cZero", "Tower.cZero", NT + "XTwApplyApply.lean", "def", "cZero"),
    ("layU", "Tower.layU", NT + "XTwApplyApply.lean", "abbrev", "layU"),
    ("muQ", "Tower.muQ", NT + "CycMemPrincIff.lean", "theorem", "UpperTheory.V.Tower.muQ"),
    ("galOfCyc", "Kum.galOfCyc", GL + "KummerTheory/GalOfCyc.lean", "theorem", "UpperTheory.V.Kum.galOfCyc"),
    ("galEmbTop", "Base.galEmbTop", GL + "SelmerTransport/GalEmbTop.lean", "theorem", "UpperTheory.V.Base.galEmbTop"),
    ("luKey", "lu_key", NT + "LayerUniq.lean", "private theorem", "lu_key"),
    ("layerUniq", "Tower.layerUniq", NT + "LayerUniq.lean", "theorem", "UpperTheory.V.Tower.layerUniq"),
    ("layerGen", "Tower.layerGen", NT + "LayerGen.lean", "theorem", "UpperTheory.V.Tower.layerGen"),
    # descent to a layer: the twisted actions and the two statements taken from the neighbouring directory
    ("IsGen", "Tower.IsGen", NT + "XTwApplyApply.lean", "def", "IsGen"),
    ("dTw", "Tower.dTw", NT + "XTwApplyApply.lean", "def", "dTw"),
    ("xTw", "Tower.xTw", NT + "XTwApplyApply.lean", "def", "xTw"),
    ("xTwApply", "Tower.xTw_apply_apply", NT + "XTwApplyApply.lean", "theorem", "xTw_apply_apply"),
    ("ShaD", "Tower.ShaD", NT + "XTwApplyApply.lean", "abbrev", "ShaD"),
    ("desc", "Tower.desc", NT + "Imports.lean", "theorem", "UpperTheory.V.Tower.desc"),
    ("shaLenInv", "shaLen_eq_shaInv", GL + "GaloisCohomologyLength/ShaLenEqShaInv.lean", "theorem", "shaLen_eq_shaInv"),
    ("shaDGen", "Tower.shaDGen", NT + "ShaDGen.lean", "theorem", "UpperTheory.V.Tower.shaDGen"),
]
# the four declarations that the embedding atlas puts into the cluster
CLUSTER = ["aDesc", "aTower", "thmBab", "thmBabK"]
QUOTED = ["aTower", "ABound", "SecondBound", "centres", "growth", "step0"]     # statements printed in the appendix
TOP = re.compile(r"^(?:@\[|/--|private |protected |noncomputable |theorem |lemma |def |abbrev |structure |class |"
                 r"instance |example |namespace |end\b|section\b|variable |open |universe |attribute |set_option )")


def sha256(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def archive_src() -> Path | None:
    """Source tree of the Lean archive: the environment variable ARCHIVE_SRC, or the entry
    `archive_src` of private/config.json (which is not part of the public tree)."""
    loc = os.environ.get("ARCHIVE_SRC")
    cfg = ROOT / "private" / "config.json"
    if not loc and cfg.exists():
        loc = json.loads(cfg.read_text(encoding="utf-8")).get("archive_src")
    if loc and Path(loc).expanduser().is_dir():
        return Path(loc).expanduser()
    return None


def statement(block: list[str], word: str) -> str:
    """A definition is quoted whole; of a theorem only the statement, up to the ':=' of its proof."""
    text = "\n".join(block).rstrip()
    if word in ("def", "abbrev", "structure"):
        return text
    depth = 0
    for i, ch in enumerate(text):
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        elif ch == ":" and depth == 0 and text[i:i + 2] == ":=":
            return text[:i].rstrip()
    raise ValueError("no ':=' in " + text[:80])


def read_archive(src: Path) -> dict:
    out = {}
    for key, shown, rel, word, head in DECLS:
        f = src / rel
        lines = f.read_text(encoding="utf-8").split("\n")
        pat = re.compile(r"^" + re.escape(word) + r"\s+" + re.escape(head) + r"(?![\w.'₀-₉])")
        hits = [i for i, ln in enumerate(lines) if pat.match(ln)]
        assert len(hits) == 1, f"{key}: {len(hits)} matches for '{word} {head}' in {rel}"
        a = hits[0]
        b = a + 1
        while b < len(lines) and not TOP.match(lines[b]):
            b += 1
        while not lines[b - 1].strip():
            b -= 1
        out[key] = {"name": shown, "file": rel, "lines": [a + 1, b], "file_sha256": sha256(f),
                    "kind": word.split()[-1], "statement": statement(lines[a:b], word.split()[-1])}
    return out


def refresh_atlas() -> dict:
    """Where the embedding atlas places the declarations of the two directories (network)."""
    import gzip
    import struct
    import urllib.request
    sha = json.loads(subprocess.run(["gh", "api", "repos/nasqret/riemann-proof-atlas/commits/main"],
                                    capture_output=True, text=True, check=True).stdout)["sha"]

    def get(path: str) -> bytes:
        with urllib.request.urlopen(ATLAS_RAW + sha + "/" + path, timeout=120) as r:
            raw = r.read()
        return gzip.decompress(raw) if path.endswith(".gz") else raw
    idx = json.loads(get("data/lean/index.json"))
    meta = json.loads(get("data/refinement/index.json"))
    bundles = json.loads(get("data/lean/bundles.json.gz")) + json.loads(get("data/refinement/groups.json.gz"))
    topics = {t["id"]: t["label"] for t in json.loads(get("data/lean/topics.json"))}
    refined = {}
    raw = get("data/refinement/points.bin.gz")
    for o in range(0, len(raw), 15):
        i, _, _, bu, meth = struct.unpack_from("<IffHB", raw, o)
        refined[i] = (bu, "refined: " + meta["methods"][meth])
    stride, nbytes, rs = idx["pointStride"], idx["pointBytes"], idx["recordStride"]
    rows, shards = [], {}
    for sh in (376, 387):                      # the record shards that hold the two directories
        for k, r in enumerate(json.loads(get(f"data/lean/records/{sh}.json.gz"))):
            i = sh * rs + k
            mod = r.get("module", "")
            if ".AdditiveValuationNorms." not in mod and ".LayeredIsomorphisms." not in mod:
                continue
            if i // stride not in shards:
                shards[i // stride] = get(f"data/lean/points/{i // stride}.bin.gz")
            o = (i % stride) * nbytes
            bu = struct.unpack_from("<I", shards[i // stride], o + 8)[0]
            how = idx["bases"][shards[i // stride][o + 14]]
            if i in refined:
                bu, how = refined[i]
            rows.append({"row": i, "name": r["name"], "directory": mod.split(".")[-2], "line": r["line"],
                         "bundle": bundles[bu]["id"], "bundle_label": bundles[bu]["label"],
                         "subject": topics.get(bundles[bu].get("topic"), bundles[bu].get("topic")), "placed_by": how})
    assert idx["sourcePin"] == meta["sourcePin"]
    return {"atlas": ATLAS_SITE, "atlas_commit": sha, "source_pin": idx["sourcePin"], "bundle": BUNDLE,
            "declarations_in_atlas": idx["count"], "bundles_in_atlas": meta["bundles"], "rows": rows}


# ------------------------------------------------------------------------------------ examples
def val(l: int, x: Fr) -> int | None:
    """l-adic valuation of a rational number; None stands for the valuation of 0."""
    if x == 0:
        return None
    n, d, k = x.numerator, x.denominator, 0
    while n % l == 0:
        n //= l
        k += 1
    while d % l == 0:
        d //= l
        k -= 1
    return k


def mmul(a, b):
    n = len(a)
    return [[sum(a[i][k] * b[k][j] for k in range(n)) for j in range(n)] for i in range(n)]


def mpow(a, e):
    n = len(a)
    r = [[Fr(int(i == j)) for j in range(n)] for i in range(n)]
    while e:
        if e & 1:
            r = mmul(r, a)
        a = mmul(a, a)
        e >>= 1
    return r


def det(a):
    n = len(a)
    if n == 1:
        return a[0][0]
    if n == 2:
        return a[0][0] * a[1][1] - a[0][1] * a[1][0]
    return sum((-1) ** j * a[0][j] * det([row[:j] + row[j + 1:] for row in a[1:]]) for j in range(n))


def tau(l: int, u: int, g, h: int, m: int) -> int | None:
    """Length of the cokernel of (u^h g)^(l^m) - 1 on the free module Z_l^n: the valuation of its
    determinant (Lemma on Smith normal forms); None when the determinant vanishes (infinite length)."""
    n = len(g)
    w = mpow([[Fr(u) ** h * x for x in row] for row in g], l ** m)
    return val(l, det([[w[i][j] - int(i == j) for j in range(n)] for i in range(n)]))


def ilog(l: int, n: int) -> int:
    k = 0
    while l ** (k + 1) <= n:
        k += 1
    return k


def examples() -> dict:
    l, u = 3, 4
    a = val(l, Fr(u - 1))
    assert a == 1
    # Example 1: two centres, 5 and -1/2
    g1 = [[Fr(1, 4 ** 5), Fr(1)], [Fr(0), Fr(-2)]]
    R1, Z, levels = 2, 150, range(0, 5)
    m0 = ilog(l, R1) + 3
    c1 = lambda h: val(l, Fr(h - 5))            # noqa: E731   v(c_1 - h), c_1 = 5
    c2 = lambda h: val(l, Fr(2 * h + 1))        # noqa: E731   v(c_2 - h), c_2 = -1/2
    excess = {}
    for h in range(1, Z + 1):
        for m in levels:
            t = tau(l, u, g1, h, m)
            if h == 5:
                assert t is None                              # the singular twist
            else:
                assert t == R1 * (m + a) + c1(h) + c2(h), (h, m, t)      # the closed formula of the text
        excess[h] = None if h == 5 else c1(h) + c2(h)
    k = ilog(l, Z)
    exc = sorted(h for h in range(1, Z + 1) if h == 5 or c1(h) > k or c2(h) > k)
    assert exc == [5, 121] and len(exc) <= R1
    worst = max(v for h, v in excess.items() if h not in exc)
    assert worst <= k and all(excess[h] <= R1 * k for h in excess if h not in exc)
    # Example 2: a cyclic permutation, the reason for a reference layer
    g2 = [[Fr(0), Fr(0), Fr(1)], [Fr(1), Fr(0), Fr(0)], [Fr(0), Fr(1), Fr(0)]]
    R2 = 3
    table = {}
    for h in (1, 9):
        row = [tau(l, u, g2, h, m) for m in range(0, 5)]
        vh = val(l, Fr(h))
        assert row[0] == a + 1 + vh and all(row[m] == R2 * (a + m + vh) for m in range(1, 5)), row
        table[h] = row
    jumps = [table[9][m + 1] - table[9][m] for m in range(4)]
    assert jumps[0] > R2 and all(j == R2 for j in jumps[1:])
    return {"l": l, "u": u, "a": a, "ex1": {"R": R1, "Z": Z, "m0": m0, "k": k, "exceptional": exc, "excess": excess,
                                            "worst_ordinary": worst, "levels_checked": len(levels)},
            "ex2": {"R": R2, "m0": ilog(l, R2) + 3, "table": table, "jumps": jumps}, "random": random_growth()}


def cok_len(l: int, F, exps, prec: int) -> int | None:
    """Length of the cokernel of the endomorphism F of X = sum_i Z_l/l^(e_i) (e_i = None: a free
    summand): the sum of the valuations of the invariant factors of the matrix [F | diag(l^(e_i))],
    computed modulo l^prec. None if a factor vanishes to that precision (infinite length)."""
    n, mod = len(F), l ** prec
    M = [[F[i][j] % mod for j in range(n)] + [(l ** exps[i] if (i == j and exps[j] is not None) else 0)
                                              for j in range(n)] for i in range(n)]

    def vv(x):
        k = 0
        while k < prec and x % l == 0:
            x //= l
            k += 1
        return k
    total, cols = 0, list(range(2 * n))
    for r in range(n):
        v, i, j = min((vv(M[i][j]), i, j) for i in range(r, n) for j in cols)
        if v >= prec:
            return None
        total += v
        M[r], M[i] = M[i], M[r]
        inv = pow(M[r][j] // l ** v, -1, mod)
        for i2 in range(r + 1, n):
            f = (M[i2][j] // l ** v) * inv % mod          # the pivot has the least valuation, so it divides
            if f:
                M[i2] = [(a - f * b) % mod for a, b in zip(M[i2], M[r])]
        cols.remove(j)
    return total


def random_growth() -> dict:
    """Proposition on growth, tested on random modules (a free summand and non-zero torsion in each)
    with random endomorphisms that are unipotent modulo l, from the layer floor(log_l R) + 2 on (one
    layer below the archive's m_0). Finite modules are left out: there the test would be vacuous."""
    import random
    rng = random.Random(20261122)
    prec, cases, steps, sharp = 90, 0, 0, 0
    for l, u in ((2, 5), (3, 4), (5, 6)):
        for _ in range(40):
            n = rng.randint(2, 4)                            # one torsion summand, one free summand, and others
            exps = sorted([rng.choice([1, 2, 3]), None] + [rng.choice([1, 1, 2, 3, None]) for _ in range(n - 2)],
                          key=lambda e: 10 ** 6 if e is None else e)
            mod = l ** prec
            g = [[0] * n for _ in range(n)]
            for i in range(n):
                for j in range(n):
                    if i == j:
                        g[i][j] = 1 + l * rng.randint(0, 8)
                    elif i < j:                              # summand j has the larger exponent: any entry is a map
                        g[i][j] = rng.randint(0, 8)
                    elif exps[i] is None and exps[j] is not None:
                        g[i][j] = 0                          # no map from a torsion summand to a free one
                    else:                                    # exps[i] >= exps[j]: divisibility makes it a map
                        d = 0 if exps[i] is None else exps[i] - exps[j]
                        g[i][j] = l ** max(d, 1) * rng.randint(0, 8)
            h = rng.randint(0, 30)
            w = [[pow(u, h, mod) * x % mod for x in row] for row in g]
            n1 = ilog(l, n) + 2
            for _ in range(n1):                              # w := w^(l^n1)
                w = mpow_mod(w, l, mod)
            prev = cok_len(l, [[w[i][j] - int(i == j) for j in range(n)] for i in range(n)], exps, prec)
            if prev is None:
                continue
            cases += 1
            for _ in range(3):
                w = mpow_mod(w, l, mod)
                cur = cok_len(l, [[w[i][j] - int(i == j) for j in range(n)] for i in range(n)], exps, prec)
                assert cur is not None and prev <= cur <= prev + n, (l, exps, g, h, prev, cur)
                steps += 1
                sharp += cur == prev + n
                prev = cur
    assert cases >= 100
    return {"cases": cases, "steps": steps, "sharp": sharp}


def mpow_mod(a, e, mod):
    n = len(a)
    r = [[int(i == j) for j in range(n)] for i in range(n)]
    while e:
        if e & 1:
            r = [[sum(r[i][k] * a[k][j] for k in range(n)) % mod for j in range(n)] for i in range(n)]
        a = [[sum(a[i][k] * a[k][j] for k in range(n)) % mod for j in range(n)] for i in range(n)]
        e >>= 1
    return r


def figure(ex: dict) -> str:
    """TikZ: the excess sum_i v(c_i - h) of Example 1 against the twist h."""
    e1 = ex["ex1"]
    Z, k = e1["Z"], e1["k"]
    sx, sy, top = 13.0 / Z, 0.56, 6.25           # cm per twist, cm per unit of valuation, height of the arrow
    o = [r"\begin{tikzpicture}[x=1cm,y=1cm,font=\sffamily\fontsize{7.4}{9}\selectfont]"]
    o.append(r"\draw[rulegrey,line width=0.5pt] (0,0) -- (%.3f,0);" % (Z * sx + 0.15))
    for t in range(0, Z + 1, 25):
        if t:
            o.append(r"\draw[rulegrey,line width=0.5pt] (%.3f,0) -- (%.3f,-0.07) node[below,inksoft,inner sep=2pt]{%d};"
                     % (t * sx, t * sx, t))
    o.append(r"\node[below,inksoft,inner sep=2pt] at (%.3f,-0.36) {twist $h$};" % (Z * sx / 2))
    for y in range(0, 6):
        o.append(r"\draw[rulegrey,line width=0.5pt] (-0.07,%.3f) -- (0,%.3f) node[left,inksoft,inner sep=3.5pt]{%d};"
                 % (y * sy, y * sy, y))
    o.append(r"\draw[rulegrey,line width=0.5pt] (0,0) -- (0,%.3f);" % (5.6 * sy))
    o.append(r"\draw[inkfaint,line width=0.5pt,dash pattern=on 2.2pt off 1.8pt] (0,%.3f) -- (%.3f,%.3f);"
             % ((k + 0.5) * sy, Z * sx + 0.15, (k + 0.5) * sy))
    o.append(r"\node[anchor=south east,inksoft,inner sep=1.5pt] at (%.3f,%.3f) {exceptional above this line};"
             % (118 * sx, (k + 0.5) * sy))
    for h in range(1, Z + 1):
        v = e1["excess"][h]
        x = h * sx
        near5 = (h - 5) % 3 == 0                 # the stem belongs to the centre 5, otherwise to -1/2
        col = "arith" if near5 else "est"
        if v is None:
            o.append(r"\draw[%s,line width=0.9pt,-{Stealth[length=4pt,width=3.6pt]}] (%.3f,0) -- (%.3f,%.3f);"
                     % (col, x, x, top * sy))
            o.append(r"\node[anchor=west,%s,inner sep=2.5pt] at (%.3f,%.3f) {$h=5$: length $\infty$};"
                     % (col, x, (top - 0.25) * sy))
        elif v > 0:
            o.append(r"\draw[%s,line width=0.7pt] (%.3f,0) -- (%.3f,%.3f);" % (col, x, x, v * sy))
            mark = (r"\fill[%s] (%.3f,%.3f) circle (1.25pt);" if near5 else
                    r"\fill[%s] (%.3f,%.3f) ++(-1.2pt,-1.2pt) rectangle ++(2.4pt,2.4pt);")
            o.append(mark % (col, x, v * sy))
            if v >= 3:
                o.append(r"\node[above,%s,inner sep=2.2pt] at (%.3f,%.3f) {%d};" % (col, x, v * sy, h))
    o.append(r"\node[anchor=south east,inner sep=0pt] at (%.3f,%.3f) {\legdot{arith}\textcolor{inksoft}{stems near the centre $c_1=5$}"
             r"\qquad\tikz[baseline=-0.62ex]\fill[est] (-2.4pt,-2.4pt) rectangle (2.4pt,2.4pt);\hspace{3pt}"
             r"\textcolor{inksoft}{stems near the centre $c_2=-\frac12$}};" % (Z * sx + 0.15, (top + 0.55) * sy))
    o.append(r"\node[rotate=90,inksoft,inner sep=0pt] at (-0.62,%.3f) {$v_3(c_1-h)+v_3(c_2-h)$};" % (2.75 * sy))
    o.append(r"\end{tikzpicture}")
    return "\n".join(o) + "\n"


# ------------------------------------------------------------------------------------ output
def lean_url(model: dict, d: dict) -> str:
    base = model["pins"]["mirror"] + "/blob/" + model["pins"]["mirror_commit"] + "/src/"
    return base + d["file"] + "#L%d-L%d" % tuple(d["lines"])


def data_tex(conc: dict, atlas: dict, ex: dict, model: dict, cov: dict | None = None) -> str:
    out = ["% generated by scripts/build_digest.py -- do not edit"]
    for key, d in conc["declarations"].items():
        out.append(r"\expandafter\newcommand\csname LN@%s\endcsname{\href{%s}{\leanfont %s}}"
                   % (key, url_escape(lean_url(model, d)), tex_escape(d["name"])))
    files = sorted({d["file"] for d in conc["declarations"].values()})
    commit = model["pins"]["mirror_commit"]
    num = lambda n: f"{n:,}".replace(",", "{,}")       # noqa: E731
    out += [r"\newcommand{\Pin}{%s}" % commit[:8],
            r"\newcommand{\PinUrl}{%s}" % url_escape(model["pins"]["mirror"] + "/tree/" + commit + "/src")]
    if ATLAS:
        rows = atlas["rows"]
        av = [r for r in rows if r["directory"] == "AdditiveValuationNorms"]
        subj: dict[str, int] = {}
        for r in av:
            subj[r["subject"]] = subj.get(r["subject"], 0) + 1
        order = sorted(subj.items(), key=lambda kv: (-kv[1], kv[0]))
        inb = [r for r in rows if r["bundle"] == atlas["bundle"]]
        assert sorted(r["name"].split(".")[-1] for r in inb) == sorted(
            conc["declarations"][k]["name"].split(".")[-1] for k in CLUSTER), "the cluster changed in the atlas"
        tiers = {n["declaration"].split(".")[-1]: n["tier"] for n in model["nodes"] if n["id"].startswith("tower-")}
        named = [conc["declarations"][k]["name"].split(".")[-1] for k in CLUSTER]
        checked = [n for n in named if tiers.get(n) == "checked"]
        covered = [n for n in named if tiers.get(n) == "covered"]
        assert len(checked) + len(covered) == len(CLUSTER), tiers
        out += [
            r"\newcommand{\AtlasUrl}{%s}" % url_escape(ATLAS_SITE),
            r"\newcommand{\AtlasClusterUrl}{%s}" % url_escape(ATLAS_SITE + "#theorem=%d" % min(r["row"] for r in inb)),
            r"\newcommand{\AtlasCommit}{%s}" % atlas["atlas_commit"][:8],
            r"\newcommand{\AtlasDecls}{%s}" % num(atlas["declarations_in_atlas"]),
            r"\newcommand{\AtlasBundles}{%s}" % num(atlas["bundles_in_atlas"]),
            r"\newcommand{\ClusterSize}{%d}" % len(inb),
            r"\newcommand{\DirDecls}{%d}" % len(av),
            r"\newcommand{\NChecked}{%d}" % len(checked),
            r"\newcommand{\NCovered}{%d}" % len(covered),
            r"\newcommand{\SubjectCount}{%d}" % len(order),
            r"\newcommand{\SubjectRows}{%s}" % "".join(r"%s & %d\\" % (tex_escape(s), n) for s, n in order),
        ]
    out += [r"\newcommand{\DirFiles}{%d}" % conc["directory"]["files"],
            r"\newcommand{\DirLines}{%s}" % num(conc["directory"]["lines"]),
            r"\newcommand{\ConcDecls}{%d}" % len(conc["declarations"]),
            r"\newcommand{\ConcFiles}{%d}" % len(files)]
    if EXAMPLES:
        e1, e2 = ex["ex1"], ex["ex2"]
        out += [
            r"\newcommand{\ExZ}{%d}" % e1["Z"],
            r"\newcommand{\ExK}{%d}" % e1["k"],
            r"\newcommand{\ExMzero}{%d}" % e1["m0"],
            r"\newcommand{\ExLevels}{%d}" % e1["levels_checked"],
            r"\newcommand{\ExExc}{%s}" % " and ".join(str(h) for h in e1["exceptional"]),
            r"\newcommand{\ExWorst}{%d}" % e1["worst_ordinary"],
            r"\newcommand{\ExTwoMzero}{%d}" % e2["m0"],
            r"\newcommand{\ExTwoRowOne}{%s}" % " & ".join(str(x) for x in e2["table"][1]),
            r"\newcommand{\ExTwoRowNine}{%s}" % " & ".join(str(x) for x in e2["table"][9]),
            r"\newcommand{\ExTwoJump}{%d}" % e2["jumps"][0],
            r"\newcommand{\RandCases}{%d}" % ex["random"]["cases"],
            r"\newcommand{\RandSteps}{%d}" % ex["random"]["steps"],
            r"\newcommand{\RandSharp}{%d}" % ex["random"]["sharp"],
        ]
    if cov:
        out += [r"\newcommand{\UnitMembers}{%d}" % cov["used"],
                r"\newcommand{\UnitInDir}{%d}" % cov["in_directory"],
                r"\newcommand{\UnitOutside}{%d}" % (cov["used"] - cov["in_directory"]),
                r"\newcommand{\UnitInNote}{%d}" % cov["in_note"],
                r"\newcommand{\UnitElsewhere}{%d}" % cov["elsewhere"],
                r"\newcommand{\ElsewhereRows}{%s}" % "".join(r"%s & %d\\" % (tex_escape(t), n) for t, n in cov["subjects"]),
                r"\newcommand{\UnitProofs}{%d}" % cov["proofs"]["proofs"],
                r"\newcommand{\UnitSteps}{%d}" % cov["proofs"]["leaf_steps"]]
        assert cov["proofs"]["leaf_steps_quoting_their_lines"] == cov["proofs"]["leaf_steps"]
        assert cov["proofs"]["lines_no_step_accounts_for"] == 0
    # the concordance table and the quoted statements
    tab = []
    for key, d in conc["declarations"].items():
        tab.append(r"\crow{%s}{\lean{%s}}{%s}{%d--%d}" % (key, key, tex_escape(d["file"].split("/")[-1]), *d["lines"]))
    out.append(r"\newcommand{\ConcordanceRows}{%s}" % "\n".join(tab))
    for key in QUOTED:
        out.append(r"\expandafter\newcommand\csname LQ@%s\endcsname{%s}" % (key, quote_tex(conc["declarations"][key]["statement"])))
    return "\n".join(out) + "\n"


def quote_tex(s: str) -> str:
    """A Lean statement as a block of typewriter lines (indentation kept, long lines may break)."""
    lines = []
    for ln in s.split("\n"):
        ind = len(ln) - len(ln.lstrip(" "))
        lines.append(r"\leanquoteline{%d}{%s}" % (ind, lean_escape(ln.lstrip(" "))))
    return "".join(lines)


def lean_escape(s: str) -> str:
    rep = {"\\": r"\textbackslash{}", "{": r"\{", "}": r"\}", "_": r"\_", "&": r"\&", "%": r"\%", "#": r"\#",
           "^": r"\textasciicircum{}", "~": r"\textasciitilde{}", "$": r"\$"}
    return "".join(rep.get(ch, ch) for ch in s)


def directory_stats(src: Path) -> dict:
    files = sorted((src / A).glob("*.lean"))
    return {"path": A, "files": len(files), "lines": sum(len(f.read_text(encoding="utf-8").split("\n")) - 1 for f in files)}


# The outline of the chapter: every declaration of the unit belongs to exactly one node (checked). The edges and
# what a node takes for granted are computed from the dependencies recorded in unit.json.
OUTLINE = [
    ("setting", "Setting", "modules over the l-adic integers, twisted lengths, the reference layer",
     ["GenBy", "jZero", "IsLevel", "cokLen", "InPow", "Unip", "twLen", "vl"]),
    ("presentation", "Presentation", "the length of a cokernel is at most the valuation of a determinant",
     ["range", "lift"]),
    ("eigenvalues", "Eigenvalues", "the determinant of tS - 1 is the product of the t z_i - 1", ["detFactor"]),
    ("centre", "One centre for each eigenvalue", "lifting the exponent, the ultrametric inequality, compactness",
     ["lteNorm", "normDvd", "normAddVal", "units", "helly", "ball", "normVal", "dvdNorm", "vlProd", "detBound", "level"]),
    ("unipotence", "Unipotence", "(gamma - 1)^R vanishes modulo l; stable under twists",
     ["cokL", "nilLen", "nilSucc", "nilLt", "unipPow", "twist"]),
    ("congruences", "Congruences", "g^(l^n) is 1 modulo l^2 from a small layer on", ["frob", "powIn"]),
    ("step", "One step", "from one layer to the next the length grows by at most R", ["phi", "step"]),
    ("growth", "Theorem B", "every layer is controlled by the reference layer", ["mono", "growth", "twgrowth"]),
    ("centres", "Theorem A and Corollary C", "one set of centres for all layers; at most R exceptional twists",
     ["centres", "centresnorm", "vlNorm"]),
    ("dual", "The dual module", "locally nilpotent on a discrete module, so unipotent on its dual",
     ["qzInj", "torsFin", "dualDiv", "dualUnip", "xUnip"]),
    ("descent", "Descent to a layer", "the length over a layer is a twisted length on the Iwasawa module",
     ["Descends", "step0", "descends", "eqTwLen", "qzSep", "exactDual", "simpleDual", "leDual", "lenDual", "dualKer",
      "cokerDual", "pgIndex", "pgExists", "pgEmult", "princGen", "luKey", "layerUniq", "layerGen", "cycRange"]),
    ("reference", "The reference layer", "the length at one layer is bounded by a second cohomology group", ["shaLeV"]),
    ("tower", "Theorem D", "class groups in the cyclotomic tower", ["genLevel", "memLev", "aDesc", "aTower"]),
]


def outline(conc: dict, unit: dict) -> dict:
    """The nodes partition the unit: a member is in the node that lists its key, or, when this note treats one
    part of the unit, in the node of the subject (ELSEWHERE) that owns its source file."""
    site = lambda ident: (ident.rsplit(":", 2)[0].replace(".", "/") + ".lean", int(ident.rsplit(":", 2)[1]))  # noqa: E731
    key_at = {(d["file"], d["lines"][0]): k for k, d in conc["declarations"].items()}
    members = {m["id"]: m for m in unit["members"]}
    node_of = {}
    for nid, _, _, keys in OUTLINE:
        for k in keys:
            assert k in conc["declarations"] and k not in node_of, f"outline: {k} is unknown or in two nodes"
            node_of[k] = nid
    file_node = {f: eid for eid, _, files in ELSEWHERE for f in files}
    where, missing = {}, []
    for m in unit["members"]:
        k = key_at.get((m["file"], m["lines"][0]))
        n = node_of.get(k) or file_node.get(m["file"].rsplit("/", 1)[-1])
        if n is None:
            missing.append(m["name"])
        where[m["id"]] = n
    extra = sorted(set(node_of) - {key_at.get((m["file"], m["lines"][0])) for m in unit["members"]})
    assert not missing and not extra, f"outline is not a partition of the unit: missing {sorted(missing)}, not in the unit {extra}"
    ids = [nid for nid, *_ in OUTLINE] + [eid for eid, *_ in ELSEWHERE]
    edges: dict[tuple[str, str], int] = {}
    granted: dict[str, dict] = {nid: {"cited": set(), "other": set()} for nid in ids}
    for m in unit["members"]:
        here = where[m["id"]]
        for u in m["uses"]:
            if u in members:
                there = where[u]
                if there != here:
                    edges[(there, here)] = edges.get((there, here), 0) + 1
            elif site(u) in key_at:
                granted[here]["cited"].add(key_at[site(u)])
            else:
                granted[here]["other"].add(u)
    nodes = [{"id": nid, "title": title, "text": text, "declarations": keys,
              "takes_for_granted": sorted(granted[nid]["cited"]),
              "other_declarations_used": len(granted[nid]["other"])} for nid, title, text, keys in OUTLINE]
    if ELSEWHERE:
        count = collections.Counter(where.values())
        for n in nodes:
            n.update(in_this_note=True, members=count[n["id"]])
        nodes += [{"id": eid, "title": title, "text": "not treated in this note", "declarations": [],
                   "takes_for_granted": sorted(granted[eid]["cited"]), "other_declarations_used": len(granted[eid]["other"]),
                   "in_this_note": False, "members": count[eid]} for eid, title, _ in ELSEWHERE]
    return {"nodes": nodes, "edges": [{"from": a, "to": b, "uses": n} for (a, b), n in sorted(edges.items())]}


LETTERED = [("Theorem A", "t:A"), ("Theorem B", "t:B"), ("Cor. C", "t:C"), ("Theorem D", "t:D"), ("Input 1", "i:1"),
            ("Input 2a", "i:2a"), ("Input 2b", "i:2b"), ("Input 2", "i:2"), ("Input 3", "i:3")]


def reader_index(conc: dict, tex: str, aux: str, cov: dict | None, pdf: Path) -> dict:
    """What a reader that shows the note beside the Lean text needs: for every cited declaration, where the
    note treats it (the words of the concordance table, the page, the named destination in the PDF)."""
    labels = {m.group(1): {"number": m.group(2), "page": int(m.group(3)), "dest": m.group(4)}
              for m in re.finditer(r"\\newlabel\{([^}]+)\}\{\{([^}]*)\}\{(\d+)\}\{(?:[^{}]|\{[^{}]*\})*\}\{([^}]*)\}", aux)}
    where = dict(re.findall(r"\\cs\{(\w+)\}\{((?:[^{}]|\{[^{}]*\})*)\}", tex))
    unit_sites = set()
    # the identity of a declaration in the archive, MODULE:LINE:COLUMN: for the members of the unit from unit.json,
    # for the others from ids.json (supplied by the reading project and checked against the archive when received)
    ident = json.loads((D / "ids.json").read_text(encoding="utf-8")) if (D / "ids.json").exists() else {}
    member_id = {}
    if cov:
        unit = json.loads((D / "unit.json").read_text(encoding="utf-8"))
        unit_sites = {(m["file"], m["lines"][0]) for m in unit["members"]}
        member_id = {(m["file"], m["lines"][0]): m["id"] for m in unit["members"]}
    rows, items = [], {}
    for key, d in conc["declarations"].items():
        raw = where[key]
        refs = re.findall(r"\\ref\{([^}]+)\}", raw)
        label = next((lab for words, lab in LETTERED if raw.replace("~", " ").startswith(words)), refs[0] if refs else None)
        text = re.sub(r"\\ref\{([^}]+)\}", lambda m: labels[m.group(1)]["number"], raw).replace("~", " ").replace("\\,", " ")
        assert label in labels, f"{key}: no anchor for '{raw}'"
        items.setdefault(label, {"item": label, "title": re.split(r"[,(]", text)[0].strip(), "page": labels[label]["page"],
                                 "dest": labels[label]["dest"], "declarations": []})["declarations"].append(key)
        did = member_id.get((d["file"], d["lines"][0])) or ident.get(key)
        assert did is None or did.rsplit(":", 2)[:2] == [d["file"][:-5].replace("/", "."), str(d["lines"][0])], f"{key}: {did}"
        rows.append({"key": key, "id": did, "name": d["name"], "kind": d["kind"], "file": d["file"], "lines": d["lines"],
                     "in_unit": (d["file"], d["lines"][0]) in unit_sites, "item": label, "where": text,
                     "page": labels[label]["page"], "dest": labels[label]["dest"]})
    editions = [{"file": f"editions/{f.name}", "sha256": sha256(f)} for f in sorted((D / "editions").glob("*.pdf"))]
    return {"schema": 1, "digest": conc["digest"], "archive_commit": conc["archive_commit"],
            "pdf": f"{DIGEST}.pdf", "pdf_sha256": sha256(pdf), "pages": None, "editions": editions,
            "unit": None if not cov else {"ledger": unit["ledger"], "id": unit["unit"], "used_members": cov["used"]},
            "items": sorted(items.values(), key=lambda i: (i["page"], i["item"])),
            "outline": None if not cov else outline(conc, unit), "declarations": rows}


def unit_coverage(conc: dict) -> dict | None:
    """Gate N-C (coverage of a note). unit.json lists the declarations of the unit of the reading project's
    ledger that this note is the note of (written by the private gold test from a dossier). Every member
    that the final theorems use must be in the concordance, hence cited in the text."""
    f = D / "unit.json"
    if not f.exists():
        return None
    unit = json.loads(f.read_text(encoding="utf-8"))
    sites = {(d["file"], d["lines"][0]) for d in conc["declarations"].values()}
    used = [m for m in unit["members"] if m["scope"] == "used"]
    later = {f for _, _, files in ELSEWHERE for f in files}
    here = [m for m in used if (m["file"], m["lines"][0]) in sites]
    other = [m for m in used if (m["file"], m["lines"][0]) not in sites and m["file"].rsplit("/", 1)[-1] in later]
    subjects = [(title, sum(1 for m in other if m["file"].rsplit("/", 1)[-1] in files)) for _, title, files in ELSEWHERE]
    return {"proofs": unit["structured_proofs"], "members": len(unit["members"]), "used": len(used), "subjects": subjects,
            "in_note": len(here), "elsewhere": len(other), "in_directory": sum(1 for m in used if m["file"].startswith(A)),
            "missing": sorted(m["name"] for m in used if m not in here and m not in other),
            "different_lines": sorted(m["name"] for m in used for d in conc["declarations"].values()
                                      if (d["file"], d["lines"][0]) == (m["file"], m["lines"][0]) and d["lines"] != m["lines"])}


_FIRST = {"A": A, "DECLS": DECLS, "CLUSTER": CLUSTER, "QUOTED": QUOTED, "OUTLINE": OUTLINE, "LETTERED": LETTERED}


# The signature rule (owner, 23 November 2026). A note never changes the number of arguments of a function that the
# archive defines, and never states a hypothesis of a theorem outside its statement. NOTATION registers, per key of
# the concordance, how the note writes a definition that has explicit arguments in Lean:
#   {"macro": name, "slots": [Lean names of the explicit arguments, in the order of the macro's slots], "symbol": the bare symbol}
#       the note defines \newcommand{\name}[n]{…} and writes the function only through it;
#   {"written": how it is written, "shows": [Lean names, all of them], "forbid": [patterns of a shorter way of writing it]}
#       a notation without a macro of its own.
# A definition with explicit arguments that has no entry is listed as open by every build, with the count.
NOTATION: dict = {}
_FIRST_NOTATION = {
    "twLen": {"macro": "tw", "slots": ["γ", "u", "e", "m"], "symbol": "\\tau"},
    "jZero": {"macro": "mz", "slots": ["l", "R"], "symbol": "m_0"},
    "vl": {"written": "v_\\ell(x)", "shows": ["l", "x"], "forbid": [r"(?<![A-Za-z\\_])v(?:\\bigl|\\Bigl|\\big)?\("]},
}
DEF_KINDS = ("def", "abbrev", "structure", "class", "inductive", "opaque")


def group_end(s: str, i: int) -> int:
    """The index of the brace that closes the group opened at s[i] == '{'; -1 when there is none."""
    depth, j = 0, i
    while j < len(s):
        if s[j] == "\\":
            j += 2
            continue
        depth += (s[j] == "{") - (s[j] == "}")
        if depth == 0:
            return j
        j += 1
    return -1


def signature_gate(tex: str, conc: dict) -> tuple:
    """The problems of a note under the signature rule, and the definitions that are not under the gate yet."""
    sfile = D / "signatures.json"
    if not sfile.exists():
        return ["signatures.json is missing (python3 -B private/signature_audit.py)"], []
    sigs = json.loads(sfile.read_text(encoding="utf-8"))
    if sigs["archive_commit"] != conc["archive_commit"] or set(sigs["declarations"]) != set(conc["declarations"]):
        return ["signatures.json was made for another concordance (python3 -B private/signature_audit.py)"], []
    body = re.sub(r"(?<!\\)%.*", "", tex)
    problems, opened = [], []
    for k, v in sigs["declarations"].items():
        names = [b.get("name") or b.get("type") for b in v["binders"] if b["kind"] == "explicit"]
        if v["kind"] not in DEF_KINDS or not names:
            continue
        nt = NOTATION.get(k)
        if nt is None:
            opened.append(k)
            continue
        said = nt.get("slots") if "macro" in nt else nt.get("shows")
        if sorted(said or []) != sorted(names):
            problems.append(f"{k}: its notation shows the arguments {', '.join(said or []) or 'none'}; Lean's explicit arguments are "
                            f"{', '.join(names)}: the number of arguments of a defined function is never changed")
            continue
        if "macro" in nt:
            m = re.search(r"\\newcommand\{\\%s\}\[(\d)\]\{" % nt["macro"], body)
            end = group_end(body, m.end() - 1) if m else -1
            if not m or end < 0 or int(m.group(1)) != len(names):
                problems.append(f"{k}: the note does not define \\{nt['macro']} with {len(names)} arguments")
                continue
            form = body[m.end():end]
            if re.search(r"\\%s(?![A-Za-z])" % nt["macro"], form) or (nt.get("symbol") and nt["symbol"] not in form):
                problems.append(f"{k}: the definition of \\{nt['macro']} calls itself or does not hold its symbol")
                continue
            hidden = [f"#{i + 1} ({said[i]})" for i in range(len(names)) if f"#{i + 1}" not in form]
            if hidden:
                problems.append(f"{k}: \\{nt['macro']} does not display its argument {', '.join(hidden)}")
            rest = body[:m.start()] + body[end + 1:]
            for u in re.finditer(r"\\%s(?![A-Za-z])" % nt["macro"], rest):
                j, got = u.end(), 0
                while got < len(names):
                    j += len(rest[j:]) - len(rest[j:].lstrip())
                    e = group_end(rest, j) if rest[j:j + 1] == "{" else -1
                    if e < 0:
                        break
                    j, got = e + 1, got + 1
                if got < len(names):
                    problems.append(f"{k}: \\{nt['macro']} is written with {got} of its {len(names)} arguments (line {rest.count(chr(10), 0, u.start()) + 1} or near)")
            raw = len(re.findall(re.escape(nt["symbol"]) + (r"(?![A-Za-z])" if nt["symbol"][-1:].isalpha() else ""), rest)) if nt.get("symbol") else 0
            if raw:
                problems.append(f"{k}: its symbol is written by hand in {raw} places, past \\{nt['macro']}, which shows every argument")
        for pat in nt.get("forbid", []):
            n = len(re.findall(pat, body))
            if n:
                problems.append(f"{k}: written in a shorter way than {nt['written']} in {n} places")
    return problems, opened


def configure(slug: str) -> None:
    """Point the builder at one digest: the first one from this file, any other from digests/<slug>/spec.py."""
    global DIGEST, D, A, DECLS, CLUSTER, QUOTED, OUTLINE, LETTERED, ATLAS, EXAMPLES, ELSEWHERE, NOTATION
    DIGEST, D = slug, ROOT / "digests" / slug
    if slug == FIRST:
        A, DECLS, CLUSTER, QUOTED, OUTLINE, LETTERED = (_FIRST[k] for k in ("A", "DECLS", "CLUSTER", "QUOTED", "OUTLINE", "LETTERED"))
        ATLAS, EXAMPLES, ELSEWHERE, NOTATION = True, True, [], _FIRST_NOTATION
    else:
        spec = runpy.run_path(str(D / "spec.py"))
        A, DECLS, OUTLINE = spec["DIRECTORY"], spec["DECLS"], spec["OUTLINE"]
        QUOTED, LETTERED, ELSEWHERE = spec.get("QUOTED", []), spec.get("LETTERED", []), spec.get("ELSEWHERE", [])
        CLUSTER, ATLAS, EXAMPLES, NOTATION = [], False, False, spec.get("NOTATION", {})


def main() -> int:
    """Every digest named on the command line, or all of them."""
    named = [a for a in sys.argv[1:] if not a.startswith("--")]
    slugs = named or sorted(p.name for p in (ROOT / "digests").iterdir() if (p / f"{p.name}.tex").exists())
    status = 0
    for slug in slugs:
        configure(slug)
        status |= build()
    return status

def build() -> int:
    args = {a for a in sys.argv[1:] if a.startswith("--")}
    model = json.loads((ROOT / "data/model.json").read_text(encoding="utf-8"))
    D.mkdir(parents=True, exist_ok=True)
    cfile, afile = D / "concordance.json", D / "atlas-cluster.json"
    src = archive_src()
    if "--refresh" in args:
        if src is None:
            print("digest: --refresh needs the source of the Lean archive (ARCHIVE_SRC)")
            return 1
        conc = {"digest": DIGEST, "archive_commit": model["pins"]["mirror_commit"],
                "directory": directory_stats(src), "declarations": read_archive(src)}
        cfile.write_text(json.dumps(conc, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    if "--refresh-atlas" in args:
        afile.write_text(json.dumps(refresh_atlas(), indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    conc = json.loads(cfile.read_text(encoding="utf-8"))
    atlas = json.loads(afile.read_text(encoding="utf-8")) if ATLAS else None
    problems = []
    if conc["archive_commit"] != model["pins"]["mirror_commit"] or (ATLAS and atlas["source_pin"] != conc["archive_commit"]):
        problems.append("the concordance, the atlas and the model do not name the same commit of the archive")
    if [k for k, *_ in DECLS] != list(conc["declarations"]):
        problems.append("concordance.json does not list the declarations of DECLS (run --refresh)")
    if src is not None and not problems:
        now = read_archive(src)
        diff = [k for k in now if now[k] != conc["declarations"][k]]
        if diff or directory_stats(src) != conc["directory"]:
            problems.append("the archive differs from concordance.json: " + ", ".join(diff))
    cov = unit_coverage(conc)
    if cov and (cov["missing"] or cov["different_lines"]):
        problems.append("members of the unit that the concordance does not account for: "
                        + ", ".join(cov["missing"] + cov["different_lines"]))
    ex = examples() if EXAMPLES else None
    tex = (D / f"{DIGEST}.tex").read_text(encoding="utf-8")
    wrong, opened = signature_gate(tex, conc)              # the signature rule: no argument of a defined function is dropped
    problems += wrong
    gate = ("; signature rule: %d notations checked" % len(NOTATION)
            + (", %d definitions with explicit arguments not under the gate yet" % len(opened) if opened else ", none open"))
    if "--check" in args:
        said = ("" if not cov else ", %d of the %d used members of its unit unaccounted for" % (len(cov["missing"]), cov["used"])
                if cov["missing"] else ", all %d used members of its unit among them" % cov["used"] if not cov["elsewhere"]
                else ", %d of the %d used members of its unit among them and the other %d assigned to notes to come"
                % (cov["in_note"], cov["used"], cov["elsewhere"]))
        print("digest: %s: concordance of %d declarations%s%s%s%s"
              % (DIGEST, len(conc["declarations"]), " compared with the archive" if src else " (archive not present)", said,
                 ("; examples recomputed" if EXAMPLES else "") + gate, "" if not problems else " -- PROBLEMS: " + "; ".join(problems)))
        return 1 if problems else 0
    (D / "data.tex").write_text(data_tex(conc, atlas, ex, model, cov), encoding="utf-8")
    if EXAMPLES:
        (D / "figure.tex").write_text(figure(ex), encoding="utf-8")
    used = set(re.findall(r"\\lean\{([^}]+)\}", tex))
    unknown = sorted(used - set(conc["declarations"]))
    if unknown:
        problems.append("unknown Lean keys in the text: " + ", ".join(unknown))
    unused = sorted(set(conc["declarations"]) - used - {"jZero"})
    if unused:
        problems.append("declarations of the concordance never cited in the text: " + ", ".join(unused))
    missing = check_notation(tex)
    if missing:
        problems.append("symbols used in the text but absent from the notation list: " + ", ".join(missing))
    build = D / "build"
    build.mkdir(exist_ok=True)
    env = dict(os.environ, SOURCE_DATE_EPOCH="1795300000", FORCE_SOURCE_DATE="1")
    r = subprocess.run(["latexmk", "-lualatex", "-interaction=nonstopmode", "-halt-on-error", "-outdir=build",
                        f"{DIGEST}.tex"], cwd=D, capture_output=True, text=True, env=env, timeout=900)
    logf = build / f"{DIGEST}.log"
    log = logf.read_text(encoding="utf-8", errors="replace") if logf.exists() else ""
    if r.returncode != 0:
        print(r.stdout[-3500:])
        print("digest: LaTeX failed")
        return 1
    shutil.copyfile(build / f"{DIGEST}.pdf", D / f"{DIGEST}.pdf")
    info = subprocess.run(["pdfinfo", str(D / f"{DIGEST}.pdf")], capture_output=True, text=True).stdout
    pages = int(re.search(r"Pages:\s+(\d+)", info).group(1))
    index = reader_index(conc, tex, (build / f"{DIGEST}.aux").read_text(encoding="utf-8"), cov, D / f"{DIGEST}.pdf")
    if "--edition" in args:       # keep this PDF as a published edition, named by its hash, and list it in the index
        (D / "editions").mkdir(exist_ok=True)
        shutil.copyfile(D / f"{DIGEST}.pdf", D / "editions" / f"{DIGEST}-{sha256(D / (DIGEST + '.pdf'))[:12]}.pdf")
        index = reader_index(conc, tex, (build / f"{DIGEST}.aux").read_text(encoding="utf-8"), cov, D / f"{DIGEST}.pdf")
    index["pages"] = pages
    (D / "reader.json").write_text(json.dumps(index, ensure_ascii=False, indent=1) + "\n", encoding="utf-8")
    if PAGES is not None and pages != PAGES:
        problems.append(f"{pages} pages instead of {PAGES}")
    over = re.findall(r"Overfull \\hbox \(([\d.]+)pt too wide\)", log)
    if any(float(x) > 1.0 for x in over):
        problems.append(f"overfull boxes: {over}")
    loose = [int(x) for x in re.findall(r"Underfull \\hbox \(badness (\d+)\)", log)]
    if any(x >= 4000 for x in loose):
        problems.append(f"very loose lines (badness {sorted(loose, reverse=True)[:5]})")
    if re.search(r"undefined references|Missing character|multiply defined", log):
        problems.append(f"undefined references, duplicate labels or missing glyphs (see digests/{DIGEST}/build/{DIGEST}.log)")
    print(f"digest: digests/{DIGEST}/{DIGEST}.pdf, {pages} pages, {(D / (DIGEST + '.pdf')).stat().st_size // 1024} KiB{gate}"
          + ("" if not problems else " -- PROBLEMS: " + "; ".join(problems)))
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
