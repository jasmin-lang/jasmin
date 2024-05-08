#!/usr/bin/env python3
#
# This script extracts the guaranteed constant-time (if a register is set) instructions from the Intel/ARM pages.
# It required the following non-stdlib packages:
#   requests, beautifulsoup4, tqdm
# It also assumes it is run inside of the compiler/scripts directory and that a "../jasminc" binary exists.
#

import sys
import subprocess
import json
import re
import requests

from enum import Enum
from base64 import b64decode
from pathlib import Path
from operator import itemgetter
from typing import List, Tuple, Set, Mapping, Optional
from tqdm import tqdm
from bs4 import BeautifulSoup


class wsize(Enum):
    U8 = "b"
    U16 = "w"
    U32 = "l"
    U64 = "q"


class velem(Enum):
    VE8 = "b"
    VE16 = "w"
    VE32 = "d"
    VE64 = "q"


class velem_long(Enum):
    VE8 = "bw"
    VE16 = "wd"
    VE32 = "dq"
    VE64 = "qdq"


class condt(Enum):
    O = "o"
    NO = "no"
    B = "b"
    NB = "nb"
    E = "e"
    NE = "ne"
    BE = "be"
    NBE = "nbe"
    S = "s"
    NS = "ns"
    P = "p"
    NP = "np"
    L = "l"
    NL = "nl"
    LE = "le"
    NLE = "nle"


def x86_extract_doitm() -> List[Tuple[str, int]]:
    """Extract a list of instruction + opcode pairs from the Intel website."""
    req = requests.get("https://www.intel.com/content/www/us/en/developer/articles/technical/software-security-guidance/resources/data-operand-independent-timing-instructions.html")
    soup = BeautifulSoup(req.content, "lxml")
    table = soup.find("div", class_="articlepara").find("table")
    results = []
    for tr in table.find_all("tr")[2:]:
        instr_td, opcode_td = tr.find_all("td")
        instruction = str(instr_td.text).strip()
        opcode = int(str(opcode_td.text).strip(), 16)
        results.append((instruction, opcode))
    return results


def x86_extract_opcodes(link: str, instruction: str) -> Set[str]:
    """Given a link to an instruction page and the mnemonic, extract all of the opcode fields."""
    pattern = re.compile(fr"\b{instruction}\b")
    req = requests.get(link)
    req.raise_for_status()
    soup = BeautifulSoup(req.content, "lxml")
    opcodes = set()
    for table in soup.find_all("table"):
        head_tr = table.find("tr")
        if "Instruction" not in head_tr.text:
            continue
        for tr in table.find_all("tr")[1:]:
            tds = tr.find_all("td")[:2]
            s0, s1 = str(tds[0].text).upper(), str(tds[1].text).upper()
            if pattern.search(s0) or pattern.search(s1):
                opcodes.add(s0.strip())
    return opcodes


def x86_extract_mnemonic_links() -> Mapping[str, str]:
    """Extract a mapping of instruction mnemonics to links."""
    req = requests.get("https://www.felixcloutier.com/x86/")
    req.raise_for_status()
    soup = BeautifulSoup(req.content, "lxml")
    instruction_table = soup.find("table")
    links = {}
    for tr in instruction_table.find_all("tr")[1:]:
        td = tr.find("td")
        a = td.find("a")
        mnemonic = str(td.text).strip()
        href = "https://www.felixcloutier.com" + a["href"]
        links[mnemonic.upper()] = href
    return links


def x86_resolve_instruction_link(instruction: str, links: Mapping[str, str]) -> Optional[str]:
    """Resolve an instruction to its link, special casing some cases."""
    # Oh lord save us, don't look at this fudge.
    cc_instructions = {"SET", "CMOV"}
    substring_instructions = ["PMOVSX", "PMOVZX", "VPBROADCASTM", "VPBROADCASTI", "VBROADCAST"]
    explicit_map = {
        "VMOVSD": "movsd",
        "VBROADCASTI128": "vpbroadcast",
        "VBROADCASTI32X2": "vpbroadcast",
        "VBROADCASTI32X4": "vpbroadcast",
        "VBROADCASTI32X8": "vpbroadcast",
        "VBROADCASTI64X2": "vpbroadcast",
        "VBROADCASTI64X4": "vpbroadcast",
    }
    if instruction in explicit_map:
        return f"https://www.felixcloutier.com/x86/{explicit_map[instruction]}"
    if instruction not in links:
        if instruction.startswith("V"):
            if instruction[1:] in links:
                return links[instruction[1:]]
            elif instruction[:-1] in links:
                return links[instruction[:-1]]
            elif instruction[1:-1] in links:
                return links[instruction[1:-1]]
        for cc_intruction in cc_instructions:
            if instruction.startswith(cc_intruction):
                return links[cc_intruction + "CC"]
        for sub_instruction in substring_instructions:
            if sub_instruction in instruction:
                return links[sub_instruction]
    else:
        return links[instruction]
    return None

def x86_validate_coverage(doitm_map):
    """
    Verify that the opcodes in the DOITM map fully cover all instruction encodings for the instructions.

    This is important, as Jasmin outputs assembly and has no direct control over the instruction encodings
    (and thus opcodes) the assembler picks. This validation function prints "BAD" in case some instruction's
    opcodes are not fully in the DOIT list.

    As of this comment (March 2024), only MOV, POP, PUSH opcodes involving some segment registers are not on
    the DOIT list. These will not be issued by Jasmin.
    """
    links = x86_extract_mnemonic_links()
    for instruction, opcodes in tqdm(doitm_map.items()):
        link = x86_resolve_instruction_link(instruction, links)
        if link is None:
            print(f"Ignoring {instruction}", file=sys.stderr)
            continue
        hex_opcodes = set(map(lambda x: f"{x:02X}", opcodes))
        extracted_opcodes = x86_extract_opcodes(link, instruction)
        covered_opcodes = set()
        for extracted in extracted_opcodes:
            for opcode in hex_opcodes:
                if opcode in extracted:
                    covered_opcodes.add(extracted)
                    break
        if covered_opcodes != extracted_opcodes:
            not_covered = extracted_opcodes.difference(covered_opcodes)
            print("BAD", instruction, link, hex_opcodes, not_covered, file=sys.stderr)

def x86():
    # Only do this once and store.
    doitm_json = Path("doitm.json")
    if doitm_json.exists() and doitm_json.is_file():
        print("doitm.json exists, will use and not validate again.", file=sys.stderr)
        with doitm_json.open("r") as f:
            doitm_list = json.load(f)
    else:
        print("Extracting... (will write into doitm.json for later use)", file=sys.stderr)
        doitm_instructions = x86_extract_doitm()
        doitm_map = {}
        for instruction, opcode in doitm_instructions:
            doitm_map.setdefault(instruction, set())
            doitm_map[instruction].add(opcode)
        x86_validate_coverage(doitm_map)
        doitm_list = list(doitm_map)
        with doitm_json.open("w") as f:
            json.dump(doitm_list, f)
    # Now compare with Jasmin supported instructions
    intrinsics_lines = subprocess.run(["../jasminc", "-help-instructions", "-arch", "x86-64"], capture_output=True, encoding="ascii").stdout.split("\n")
    name2instr = {}
    instr2name = {}
    for line in intrinsics_lines:
        if not line:
            continue
        name, instruction = line.strip().split(":")
        name2instr.setdefault(name, set())
        name2instr[name].add(instruction)
        instr2name.setdefault(instruction, set())
        instr2name[instruction].add(name)
    doit2instr = {}
    unused_doits = set()
    for instruction in doitm_list:
        if instruction == "MULX":
            instruction = "MULX_lo_hi"
        if instruction in name2instr:
            doit2instr[instruction] = name2instr[instruction]
        names = instr2name.get(instruction)
        if not names:
            unused_doits.add(instruction)
            continue
        for name in names:
            doit2instr.setdefault(name, set())
            doit2instr[name].add(instruction)
    names = set(doit2instr).union(name2instr).union(unused_doits)
    for name in sorted(names):
        instructions = doit2instr.get(name, set())
        jazz_instructions = name2instr.get(name, set())
        if not jazz_instructions:
            print(f"Not JAZZ          {name}", file=sys.stderr)
        elif not instructions:
            print(f"Not DOIT          {name} JAZZ:{jazz_instructions}", file=sys.stderr)
        elif jazz_instructions == instructions:
            print(f"Fully covered     {name} {instructions}", file=sys.stderr)
        else:
            print(f"Not fully covered {name} DOIT:{instructions} JAZZ:{jazz_instructions} DOIT-JAZZ:{instructions.difference(jazz_instructions)} JAZZ-DOIT:{jazz_instructions.difference(instructions)}", file=sys.stderr)
    print("  let is_doit_asm_op (o : asm_op) =")
    print("    match o with")
    for name in sorted(names):
        instructions = doit2instr.get(name, set())
        jazz_instructions = name2instr.get(name, set())
        if not jazz_instructions:
            print(f"    (* Not in Jasmin {name} *)")
        elif not instructions:
            if len(jazz_instructions) > 1:
                print(f"    | {name} _ -> false (* Not DOIT *)")
            else:
                print(f"    | {name} -> false (* Not DOIT *)")
        elif jazz_instructions == instructions:
            if len(instructions) > 1:
                print(f"    | {name} _ -> true")
            else:
                print(f"    | {name} -> true")
        else:
            print(f"    (* Partial, investigate! {name} {instructions} *)")


def arm():
    req = requests.get("https://documentation-service.arm.com/documentation/ddi0595/2021-12/AArch64-Registers/DIT--Data-Independent-Timing")
    req.raise_for_status()
    data = req.json()
    content = b64decode(data["content"])
    soup = BeautifulSoup(content, "lxml")
    title_ps = soup.find_all("p", string=re.compile("These instructions are"))
    instructions = set()
    for p in title_ps:
        ul = p.find_next_sibling("ul")
        li = ul.find("li")
        for span in li.find_all("span"):
            instructions.add(str(span.text).strip())
    # Now compare with Jasmin supported instructions
    intrinsics_lines = subprocess.run(["../jasminc", "-help-instructions", "-arch", "arm-m4"], capture_output=True, encoding="ascii").stdout.split("\n")
    name2instr = {}
    instr2name = {}
    for line in intrinsics_lines:
        if not line:
            continue
        name, instruction = line.strip().split(":")
        name2instr.setdefault(name, set())
        name2instr[name].add(instruction)
        instr2name.setdefault(instruction, set())
        instr2name[instruction].add(name)
    names = instructions.union(name2instr)
    print("  let is_doit_asm_op (o : asm_op) =")
    print("    match o with")
    for name in sorted(names):
        if name in name2instr and name in instructions:
            print(f"    | ARM_op({name}, _) -> true")
        elif name in name2instr:
            print(f"    | ARM_op({name}, _) -> false (* Not DIT *)")
        elif name in instructions:
            print(f"    (* Not in Jasmin {name} *)")


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print(f"Usage: {sys.argv[0]} x86|arm", file=sys.stderr)
        exit(2)
    match sys.argv[1]:
        case "x86":
            x86()
        case "arm":
            arm()