"""What a line of a statement means, by the account in Lean: for the tests of what statement.py writes.

A verdict relies on statement.py for the statement saying what the contract says. So the tests have the
account in Lean (`odespec`, SpecMain.lean) work out a statement's `ensures` line on numbers and bytes drawn
at random, and compare with a reading of the contract that does not go through statement.py."""
import os, subprocess, tempfile
import built, statement
HERE = os.path.dirname(os.path.abspath(__file__))


def account(spec_text, functions, cases):
    """What the account in Lean says of each (expression as a statement has it, {name: bytes or a number}),
    with the definitions the statement of these functions has: `bytes HEX`, `int N`, `none`, …"""
    built.built("odespec")
    with tempfile.TemporaryDirectory() as d:
        defs, path = os.path.join(d, "defs"), os.path.join(d, "cases")
        with open(defs, "w") as f: f.write("\n".join(l for l in statement.statement(spec_text, functions) if l.startswith("def ")) + "\n")
        with open(path, "w") as f:
            for e, env in cases:
                f.write(" ".join(f"{n}=b:{bytes(v).hex()}" if isinstance(v, (list, bytes)) else f"{n}=i:{v}" for n, v in env.items()) + " | " + e + "\n")
        out = subprocess.run([os.path.join(HERE, ".lake", "build", "bin", "odespec"), defs, path], capture_output=True, text=True, check=True).stdout.split("\n")[:len(cases)]
    assert len(out) == len(cases), (len(out), len(cases))
    return out


def ensures(spec_text, functions, symbol, run):
    """The expression of the line `ensuresw RUN …` of the function `symbol` in the statement."""
    lines = statement.statement(spec_text, functions)
    at = lines.index(f"fn {symbol}")
    (line,) = [l for l in lines[at:] if l.startswith(f"ensuresw {run} ")][:1]
    return line[len(f"ensuresw {run} "):]
