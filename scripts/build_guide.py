#!/usr/bin/env python3
"""Build the guide to the proof (guide/proof-guide.pdf).

    python3 -B scripts/build_guide.py          # writes guide/data.tex, runs LuaLaTeX, checks the layout

guide/proof-guide.tex is hand-written. Everything in it that is a number from the evidence, a time
or a link comes from guide/data.tex, generated here from data/model.json, assets/figures/facts.json
and data/source/*.json; Lean names are linked to pinned lines of the public mirror of the archive
(commit 40e56bab, byte-identical to the archive).

The guide is typeset for reading (11 pt on a 140 mm measure) and must be understandable on its own:
every symbol is explained where it first appears and listed in the notation on the last page. The
script therefore fails

* if a letter occurs in a formula of the text but not in the notation list (check_notation);
* if the PDF does not have exactly GUIDE_PAGES pages (so that a change of length is noticed), or
  LaTeX reports an overfull box, a very loose line, a missing glyph or an undefined reference.
"""
from __future__ import annotations

import json
import math
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
G = ROOT / "guide"
GUIDE_PAGES = 11    # ten pages of text and the page of notation

GREEK = ("alpha|beta|gamma|delta|eps|varepsilon|zeta|eta|theta|vartheta|iota|kappa|lambda|mu|nu|xi|pi|varpi|rho|"
         "sigma|tau|phi|varphi|chi|psi|omega|Gamma|Delta|Theta|Lambda|Xi|Pi|Sigma|Phi|Psi|Omega")


def _letters(tex: str) -> tuple[set[str], set[str]]:
    """Greek macros and Latin letters that occur in the mathematics of a piece of LaTeX."""
    chunks = re.findall(r"\$([^$]+)\$", tex)
    chunks += re.findall(r"\\m\{((?:[^{}]|\{(?:[^{}]|\{[^{}]*\})*\})*)\}", tex)
    chunks += re.findall(r"\\\[(.*?)\\\]", tex, re.S)
    chunks += re.findall(r"\\begin\{align\*\}(.*?)\\end\{align\*\}", tex, re.S)
    greek, latin = set(), set()
    for c in chunks:
        greek |= set(re.findall(r"\\(" + GREEK + r")(?![a-zA-Z])", c))
        c = re.sub(r"\\(?:text|mathrm|operatorname|emph|textbf|leanfont|kw|mbox|quad|qquad|pmod)\s*\{[^{}]*\}", "", c)
        c = re.sub(r"\\(?:begin|end)\{[A-Za-z*]+\}", "", c)      # the name of an environment is not a formula
        latin |= set(re.findall(r"[A-Za-z]", re.sub(r"\\[a-zA-Z]+", "", c)))
    return greek, latin


def check_notation(tex: str) -> list[str]:
    """Letters used in formulas of the text that the notation list does not mention."""
    body = re.sub(r"(?m)^%.*$", "", tex[tex.index(r"\begin{document}"):])
    cut = body.index(r"\head{Notation}")
    tg, tl = _letters(body[:cut])
    ng, nl = _letters(body[cut:])
    return sorted(tg - ng) + sorted(tl - nl)
M = "https://github.com/Deicyde/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/"
TG = "Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/"
LT = "Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/"
CB = "Development/AutomorphicArithmetic/CharacterBoxes/"

# key -> (displayed name, blueprint node id | None, explicit path#lines | None)
LEAN = {
    "main-rh": ("riemannHypothesis", "main-rh", None),
    "main-right": ("LFunction_ne_zero_of_half_lt_re", "main-right", None),
    "main-strip": ("LFunction_eq_zero_re", "main-strip", None),
    "imprimitive": ("imprimitive", "imprimitive", None),
    "strip": ("Claim.strip", "strip", None),
    "rh-right": ("rh_of_right", "rh-right", None),
    "G": ("Deduction.G", None, "Development/AutomorphicArithmetic/DedekindLFunctions/CharFamily.lean#L10-L45"),
    "mellin": ("MellinRamp", None, LT + "MellinRamp.lean#L10-L32"),
    "pole": ("poleData", "pole", None),
    "landau": ("zeroFree_of_rpow_window", "landau", None),
    "window-consumer": ("level_of_tiedWin", "window-consumer", None),
    "zero-top": ("zeroFreeAll_of_topG", "zero-top", None),
    "ischifield": ("IsChiField", None, CB + "ExistsPageN.lean#L19-L25"),
    "chainint": ("ChainInt", None, "Formalism/ThetaLiftIndependence/Statement.lean#L40-L57"),
    "minor": ("key_minor_dvd", "minor", None),
    "slope": ("slopeInequality_of", "slope", None),
    "chowla": ("chowla_selberg_period", None,
               "Development/AutomorphicSpectrum/Proofs/GeometryProofs/ChowlaSelbergPeriodStatement.lean#L9-L10"),
    "ask": ("ASK, MAIN", None, "Formalism/SizeWindowBrackets/FirstPrimeNeSecondPrime.lean#L72-L92"),
    "rank": ("RankVal", "rank", None),
    "topg": ("TopG", None, CB + "ZeroFreeAllOfTopG.lean#L12-L14"),
    "chbalance": ("ch_balance", None, LT + "ChBalance.lean#L200-L222"),
    "shares": ("Frame.Shares", None, TG + "ExplicitFormulaErrorOfHostConditions.lean#L133-L141"),
    "bounded": ("BoundedCharsPointwise", None, TG + "Analytic.lean#L136-L156"),
    "pairex": ("QH.pairEx", None, "Development/AutomorphicArithmetic/MeanSquareBounds/pairEx.lean#L112-L169"),
    "core-gm": ("core_gm", "core-gm", None),
    "supply": ("supplyChi", "supply", None),
    "vwin-def": ("VWinAt", "vwin-def", None),
    "window1": ("window1", None,
                "Development/AutomorphicArithmetic/AutomorphicVarieties/LayeredIsomorphisms/Window1.lean#L6-L58"),
    "behrend": ("hostThickExists", None,
                "Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickExists.lean#L181-L187"),
    "row-def": ("Row0b", "row-def", None),
    "row-prod": ("galoisLocalGlobalStrong_recParameter", "row-prod", None),
    "seven": ("every_character_of_literature_of_vWin", "lit", None),
}


def tex_escape(s: str) -> str:
    return s.replace("\\", r"\textbackslash{}").replace("_", r"\_").replace("&", r"\&").replace("%", r"\%")


def url_escape(u: str) -> str:
    return u.replace("%", r"\%").replace("#", r"\#")


def main() -> int:
    model = json.loads((ROOT / "data/model.json").read_text(encoding="utf-8"))
    facts = json.loads((ROOT / "assets/figures/facts.json").read_text(encoding="utf-8"))
    status = json.loads((ROOT / "data/source/status.json").read_text(encoding="utf-8"))
    scopes = json.loads((ROOT / "data/source/native-scopes.json").read_text(encoding="utf-8"))
    nodes = {n["id"]: n for n in model["nodes"]}
    out = ["% generated by scripts/build_guide.py -- do not edit"]
    for key, (name, node, path) in LEAN.items():
        url = nodes[node]["url"] if node else M + path
        assert url.startswith(M), url
        out.append(r"\expandafter\newcommand\csname LN@%s\endcsname{\href{%s}{\leanfont %s}}"
                   % (key, url_escape(url), tex_escape(name)))
    hero = facts["hero"]
    rmax = max(abs(hero["r_min"]), abs(hero["r_max"]))
    rmax_up = math.ceil(rmax * 1000) / 1000            # rounded up to three decimals
    assert rmax < rmax_up < hero["rh_band"]
    modules = re.search(r"all ([\d,]+) original modules", status["external"]).group(1)
    dirichlet = next(s for s in scopes if s["id"] == "dirichlet")["original_project_module_count"]
    asof = status["as_of"][:16].replace("T", ", ") + " UTC"
    # the sentence on the complete proof in the status box, from the record of its checks
    fp = model["status"]["full_proof"]
    axioms = r"{\leanfont propext}, {\leanfont Classical.choice}, {\leanfont Quot.sound}, the three standard axioms of Lean"
    count = modules.replace(",", "{,}")
    if fp["two_kernels"]:
        stages = fp["stages"]
        rust = next(s for s in stages if "Rust verification of the complete proof" in s["stage"])
        n_rust = re.search(r"([\d,]+) declarations", rust["outcome"]).group(1).replace(",", "{,}")
        assert any("comparison with the independent Mathlib challenge" in s["stage"] and "matched" in s["outcome"]
                   for s in stages)
        who = [s["operator"] for s in stages if "kernel replay" in s["stage"] and "ccepted" in s["outcome"]]
        assert who, "no full Lean replay in the record"
        short = [w.split()[0][0] + r".\," + " ".join(w.split()[1:]) for w in dict.fromkeys(who)]
        names = short[0] if len(short) == 1 else ", ".join(short[:-1]) + " and " + short[-1]
        verb = "reports" if len(short) == 1 else "each report"
        icon = r"\textcolor{ok}{\checkmark\checkmark}"
        line = (f"two independent kernels accepted the complete proof. In runs of the reading project the Rust kernel "
                f"NanoDA accepted all {n_rust} declarations of the exported proof, and the five statements matched an "
                f"independently written Mathlib challenge. {names} {verb} a Lean kernel replay of all {count} "
                f"modules. No axioms beyond {axioms}.")
    else:
        icon = r"\textcolor{inksoft}{$\nearrow$}"
        line = (f"A.\\,Sutherland reports a kernel replay of all {count} modules without rejections, a check of the "
                f"exported proof by NanoDA, and no axioms beyond {axioms}.")
    out += [r"\newcommand{\FullProofIcon}{%s}" % icon, r"\newcommand{\FullProofLine}{%s}" % line]
    out += [
        r"\newcommand{\Rmax}{%.3f}" % rmax_up,
        r"\newcommand{\RHband}{%.4f}" % hero["rh_band"],
        r"\newcommand{\ModuleCount}{%s}" % modules.replace(",", r"{,}"),
        r"\newcommand{\DirichletModules}{%s}" % f"{dirichlet:,}".replace(",", r"{,}"),
        r"\newcommand{\NanodaDecls}{%s}" % f"{status['independent_window']['declarations']:,}".replace(",", r"{,}"),
        r"\newcommand{\AsOf}{%s}" % asof.replace("2026-11-20", "20 November 2026"),
    ]
    # The status note of the guide names two checks made in this repository; refuse to build the
    # guide if their records do not say so.
    std = {"propext", "Classical.choice", "Quot.sound"}
    local = json.loads((ROOT / "verification/logs/axioms.json").read_text(encoding="utf-8"))
    assert local.get("build") == "passed" and not local.get("problems"), "local Lean audit did not pass"
    for name in ("Atlas.Architecture.endpoints", "Atlas.endpoints_of_supply", "Atlas.rh_of_prime_windows"):
        assert local["declarations"].get(name) == [], f"{name} is not recorded as axiom-free"
    zeta = json.loads((ROOT / "verification/logs/mathlib-zeta-axioms.json").read_text(encoding="utf-8"))
    assert zeta.get("build") == "passed" and not zeta.get("problems"), "the Mathlib instantiation did not pass"
    assert all(set(ax) <= std for ax in zeta["declarations"].values()), "non-standard axioms in the Mathlib instantiation"
    assert "Atlas.Zeta.riemannHypothesis_of_right" in zeta["declarations"]
    G.mkdir(exist_ok=True)
    (G / "data.tex").write_text("\n".join(out) + "\n", encoding="utf-8")
    missing = check_notation((G / "proof-guide.tex").read_text(encoding="utf-8"))
    if missing:
        print("guide: symbols used in the text but absent from the notation list: " + ", ".join(missing))
        return 1
    build = G / "build"
    build.mkdir(exist_ok=True)
    env = dict(os.environ, SOURCE_DATE_EPOCH="1795210380", FORCE_SOURCE_DATE="1")
    cmd = ["latexmk", "-lualatex", "-interaction=nonstopmode", "-halt-on-error", "-outdir=build",
           "proof-guide.tex"]
    r = subprocess.run(cmd, cwd=G, capture_output=True, text=True, env=env)
    log = (build / "proof-guide.log").read_text(encoding="utf-8", errors="replace") if (build / "proof-guide.log").exists() else ""
    if r.returncode != 0:
        print(r.stdout[-3000:])
        print("guide: LaTeX failed")
        return 1
    shutil.copyfile(build / "proof-guide.pdf", G / "proof-guide.pdf")
    info = subprocess.run(["pdfinfo", str(G / "proof-guide.pdf")], capture_output=True, text=True).stdout
    pages = int(re.search(r"Pages:\s+(\d+)", info).group(1))
    problems = []
    if pages != GUIDE_PAGES:
        problems.append(f"{pages} pages instead of {GUIDE_PAGES}")
    over = re.findall(r"Overfull \\hbox \(([\d.]+)pt too wide\)", log)
    if any(float(x) > 1.0 for x in over):
        problems.append(f"overfull boxes: {over}")
    loose = [int(x) for x in re.findall(r"Underfull \\hbox \(badness (\d+)\)", log)]
    if any(x >= 4000 for x in loose):
        problems.append(f"very loose lines (badness {sorted(loose, reverse=True)[:5]})")
    if re.search(r"undefined references|Missing character", log):
        problems.append("undefined references or missing glyphs (see guide/build/proof-guide.log)")
    print(f"guide: guide/proof-guide.pdf, {pages} pages, {(G / 'proof-guide.pdf').stat().st_size // 1024} KiB"
          + ("" if not problems else " -- PROBLEMS: " + "; ".join(problems)))
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
