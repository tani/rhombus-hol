#!/usr/bin/env python3
"""Audit Rhombus/HOL stdlib theorem declarations without loading the prover."""

from __future__ import annotations

import argparse
import json
import re
from collections import defaultdict
from dataclasses import asdict, dataclass
from pathlib import Path

THEOREM = re.compile(r"^theorem\s+([A-Za-z_][A-Za-z0-9_-]*):\s*$")
USE = re.compile(r"\buse\s*\(\s*\[([^]]*)\]\s*\)")
REFLEXIVE_NAMES = re.compile(r"(?:^|_)(?:refl|reflexive)$")


@dataclass(frozen=True)
class Declaration:
    file: str
    line: int
    name: str
    proposition: str
    proof: tuple[str, ...]


def declarations(path: Path) -> list[Declaration]:
    lines = path.read_text(encoding="utf-8").splitlines()
    starts = [(i, THEOREM.match(line)) for i, line in enumerate(lines)]
    starts = [(i, match) for i, match in starts if match]
    result: list[Declaration] = []
    for position, (start, match) in enumerate(starts):
        end = starts[position + 1][0] if position + 1 < len(starts) else len(lines)
        proposition: list[str] = []
        proof: list[str] = []
        in_proof = False
        for line in lines[start + 1 : end]:
            if line == "proof:":
                in_proof = True
                continue
            if not line.strip():
                if proposition and not in_proof:
                    break
                continue
            if line.lstrip().startswith("//"):
                continue
            (proof if in_proof else proposition).append(line.strip())
        result.append(
            Declaration(
                path.name,
                start + 1,
                match.group(1),
                " ".join(proposition),
                tuple(proof),
            )
        )
    return result


def strip_outer_parentheses(text: str) -> str:
    text = text.strip()
    while text.startswith("(") and text.endswith(")"):
        depth = 0
        for index, character in enumerate(text):
            depth += character == "("
            depth -= character == ")"
            if depth == 0 and index != len(text) - 1:
                return text
        text = text[1:-1].strip()
    return text


def strip_forall(proposition: str) -> str:
    if not proposition.startswith("forall "):
        return proposition
    depth = 0
    for index, character in enumerate(proposition):
        depth += character == "("
        depth -= character == ")"
        if character == ":" and depth == 0:
            return proposition[index + 1 :].strip()
    return proposition


def split_top_level(text: str, operator: str) -> tuple[str, str] | None:
    depth = 0
    for index, character in enumerate(text):
        depth += character == "("
        depth -= character == ")"
        if depth == 0 and text.startswith(operator, index):
            return text[:index].strip(), text[index + len(operator) :].strip()
    return None


def normalized(text: str) -> str:
    return re.sub(r"\s+", "", strip_outer_parentheses(text))


def reflexive_operator(proposition: str) -> str | None:
    core = strip_outer_parentheses(strip_forall(proposition))
    for operator in ("<=>", "===", "==>"):
        sides = split_top_level(core, operator)
        if sides and normalized(sides[0]) == normalized(sides[1]):
            return operator
    return None


def explicit_dependencies(declaration: Declaration) -> list[str]:
    dependencies: list[str] = []
    for line in declaration.proof:
        for match in USE.finditer(line):
            dependencies.extend(
                name.strip() for name in match.group(1).split(",") if name.strip()
            )
    return dependencies


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "root",
        nargs="?",
        type=Path,
        default=Path("rhombus-hol-stdlib/rhombus/hol/stdlib"),
    )
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()

    all_declarations = [
        declaration
        for path in sorted(args.root.glob("*.rhm"))
        for declaration in declarations(path)
    ]
    by_proposition: dict[str, list[Declaration]] = defaultdict(list)
    for declaration in all_declarations:
        by_proposition[normalized(declaration.proposition)].append(declaration)

    reflexive = []
    name_mismatches = []
    for declaration in all_declarations:
        operator = reflexive_operator(declaration.proposition)
        if operator:
            finding = {
                "file": declaration.file,
                "line": declaration.line,
                "name": declaration.name,
                "operator": operator,
            }
            reflexive.append(finding)
            if not REFLEXIVE_NAMES.search(declaration.name):
                name_mismatches.append(finding)

    duplicates = [
        [f"{item.file}:{item.line}:{item.name}" for item in group]
        for group in by_proposition.values()
        if len(group) > 1
    ]
    proof_classes = {
        "explicit": sum(bool(item.proof) for item in all_declarations),
        "implicit": sum(not item.proof for item in all_declarations),
    }
    dependency_graph = {
        f"{item.file}:{item.name}": explicit_dependencies(item)
        for item in all_declarations
        if explicit_dependencies(item)
    }

    report = {
        "theorem_count": len(all_declarations),
        "reflexive_propositions": reflexive,
        "suspicious_name_mismatches": name_mismatches,
        "duplicate_propositions": duplicates,
        "proof_classes": proof_classes,
        "explicit_dependency_graph": dependency_graph,
    }

    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(f"theorems: {report['theorem_count']}")
        print(f"proofs: {proof_classes['explicit']} explicit, {proof_classes['implicit']} implicit")
        print(f"reflexive propositions: {len(reflexive)}")
        for finding in reflexive:
            marker = " suspicious-name" if finding in name_mismatches else ""
            print(
                f"  {finding['file']}:{finding['line']} {finding['name']} "
                f"({finding['operator']}){marker}"
            )
        print(f"duplicate propositions: {len(duplicates)}")
        for group in duplicates:
            print("  " + ", ".join(group))
        print(f"explicit dependency edges: {sum(map(len, dependency_graph.values()))}")

    return bool(name_mismatches or duplicates)


if __name__ == "__main__":
    raise SystemExit(main())
