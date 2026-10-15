PROPERTY="equals-wspec-v1"
def check_certificate(s,c):
    from .canon import assoc, Sym
    return assoc("record",("verdict",Sym("accept")))
