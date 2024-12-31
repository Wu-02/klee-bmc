# TODO: this is a quick hack, it's not robust and may not work in all cases.
import re

def preprocess(source):
  """
  Deal with line continuations, insert __VERIFIER_assert declaration if it's not present.
  """
  source = source.replace("\\\n", "")

  if "void __VERIFIER_assert" not in source: # HACK
    source = "extern void __VERIFIER_assert(int cond);\n" + source

  return source

def rewrite_acsl(source):
  source = preprocess(source)

  # find single line ACSL assertions
  acsl_pattern = r'//@\s*assert\s*(.*?);'
  def replace_assertion(match) -> str:
    cond = match.group(1)
    return f'__VERIFIER_assert({cond});'
  return re.subn(acsl_pattern, replace_assertion, source)


def process_acsl(file):
  """
  Convert single-line ACSL assertions in the file to __VERIFIER_assert calls.
  For example, the ACSL assertion:
    //@ assert x > 0;
  will be converted to:
    __VERIFIER_assert(x > 0);
  """
  with open(file, 'r') as f:
    source = f.read()

  source, count = rewrite_acsl(source)
  if count > 0:
    with open(file, 'w') as f:
      f.write(source)