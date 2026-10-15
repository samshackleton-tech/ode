"""BLAKE3 domain separation binds bytes to kind and semantic revision."""
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
from ode.blake3 import blake3,derive_key
from ode.canon import Bytes,binary_hash,canonical_bytes,field,hash_of,parse
from ode.domains import REVISIONS,context
from ode.store import Reject,load_definition,load_binary


class DomainTest(unittest.TestCase):
    def test_official_hash_and_derive_key_vectors(self):
        vectors=parse((Path(__file__).parent/'blake3-vectors.sexp').read_bytes())
        ctx=field(vectors,'context').decode('utf-8')
        for length,expected_hash,expected_derived in field(vectors,'cases'):
            with self.subTest(length=length):
                data=bytes(i%251 for i in range(length))
                self.assertEqual(blake3(data),expected_hash)
                self.assertEqual(derive_key(ctx,data),expected_derived)

    def test_all_current_domains_separate_identical_bytes(self):
        payload=b'(spec (name example) (inputs (x)) (steps ()) (outputs (x)))'
        hashes=[derive_key(context(kind),payload) for kind in REVISIONS]
        self.assertEqual(len(set(hashes)),len(REVISIONS))
        self.assertNotIn(blake3(payload),hashes)

    def test_caller_selects_kind_independently_of_the_object_tag(self):
        value=parse('(spec (name same-bytes))')
        self.assertNotEqual(hash_of(value,'spec'),hash_of(value,'goal'))
        self.assertNotEqual(hash_of(value,'spec'),binary_hash(canonical_bytes(value),'w32'))
        self.assertNotEqual(binary_hash(canonical_bytes(value),'w32'),binary_hash(canonical_bytes(value),'a64'))

    def test_semantic_revision_changes_identity_without_changing_bytes(self):
        value=parse('(spec (name same-bytes))')
        before=hash_of(value,'spec');other=hash_of(value,'theory')
        with patch.dict(REVISIONS,{'spec':REVISIONS['spec']+1}):
            self.assertNotEqual(before,hash_of(value,'spec'))
            self.assertEqual(other,hash_of(value,'theory'))

    def test_kind_is_required_and_unknown_domains_stop(self):
        value=parse('(spec)')
        with self.assertRaises(TypeError):hash_of(value)
        with self.assertRaises(ValueError):hash_of(value,'unspecified')
        with self.assertRaises(ValueError):binary_hash(b'code','unspecified')

    def test_store_rejects_unkeyed_wrong_kind_and_previous_semantic_ids(self):
        value=parse('(spec (name test))');data=canonical_bytes(value)
        old_context=context('spec').rsplit('v',1)[0]+'0'
        wrong=[Bytes(blake3(data)),hash_of(value,'goal'),Bytes(derive_key(old_context,data))]
        with tempfile.TemporaryDirectory() as directory:
            for digest in wrong:
                (Path(directory)/(digest.hex()+'.sexp')).write_bytes(data)
                with self.assertRaises(Reject):load_definition(directory,digest,'spec')
            current=hash_of(value,'spec')
            (Path(directory)/(current.hex()+'.sexp')).write_bytes(data)
            self.assertEqual(load_definition(directory,current,'spec'),value)

    def test_binary_reading_binds_the_execution_model(self):
        data=b'same bytes, different instruction meanings'
        digest=binary_hash(data,'w32')
        with tempfile.TemporaryDirectory() as directory:
            (Path(directory)/(digest.hex()+'.bin')).write_bytes(data)
            from ode.canon import assoc,Sym
            cert=assoc('certificate',('binary-hash',digest),('property',Sym('equals-spec-w32-v1')))
            self.assertEqual(load_binary(directory,cert),data)
            cert[-1][1]=Sym('equals-spec-a64-v1')
            with self.assertRaises(Reject):load_binary(directory,cert)

    def test_package_manifest_separates_file_and_tree_hashes(self):
        from tests.test_game import tree_hash
        files={'a':b'alpha','b':b'beta'}
        manifest=b''.join(path.encode()+b'\0'+derive_key(context('package-file'),data)
                          for path,data in sorted(files.items()))
        self.assertEqual(tree_hash(files),derive_key(context('package-tree'),manifest))
        self.assertNotEqual(tree_hash(files),derive_key(context('package-file'),manifest))
        self.assertNotEqual(tree_hash(files),blake3(manifest))

    def test_unkeyed_primitive_is_reserved_for_standard_algorithm_tests(self):
        import ast
        root=Path(__file__).resolve().parent.parent
        allowed={'tests/test_canon.py','tests/test_blake3.py','tests/test_domains.py'}
        for folder in ('ode','game','tests','tools','examples'):
            for path in (root/folder).glob('*.py'):
                for node in ast.walk(ast.parse(path.read_text())):
                    if isinstance(node,ast.ImportFrom) and node.module and node.module.endswith('blake3'):
                        if any(alias.name in ('blake3','*') for alias in node.names):
                            self.assertIn(path.relative_to(root).as_posix(),allowed)

    def test_kernel_rejects_old_semantic_links_with_current_format(self):
        from copy import deepcopy
        from ode.kernel import Reject as KernelReject,verify
        from ode.canon import Sym
        t=parse('(theory 3 () () ())')
        g=[Sym('goal'),3,hash_of(t,'theory'),parse('((n Nat))'),parse('(eq n n)')]
        p=[Sym('proof'),3,hash_of(g,'goal'),[],parse('(derive ((refl n)))')]
        verify(t,g,p)
        old_theory=context('theory').rsplit('v',1)[0]+'0'
        mutant=deepcopy(g);mutant[2]=Bytes(derive_key(old_theory,canonical_bytes(t)))
        forged=deepcopy(p);forged[2]=hash_of(mutant,'goal')
        with self.assertRaisesRegex(KernelReject,'different theory'):
            verify(t,mutant,forged)
        old_goal=context('goal').rsplit('v',1)[0]+'0'
        forged=deepcopy(p);forged[2]=Bytes(derive_key(old_goal,canonical_bytes(g)))
        with self.assertRaisesRegex(KernelReject,'different goal'):
            verify(t,g,forged)

    def test_current_spec_domain_does_not_replace_type_validation(self):
        value=parse('(goal 3)');digest=hash_of(value,'spec')
        with tempfile.TemporaryDirectory() as directory:
            (Path(directory)/(digest.hex()+'.sexp')).write_bytes(canonical_bytes(value))
            with self.assertRaisesRegex(Reject,'expected a spec'):
                load_definition(directory,digest,'spec')

    def test_context_revision_does_not_depend_on_format_version(self):
        value=parse('(theory 3 () () ())')
        before=hash_of(value,'theory')
        with patch.dict(REVISIONS,{'theory':REVISIONS['theory']+1}):
            self.assertNotEqual(before,hash_of(value,'theory'))
        self.assertEqual(value[1],3)


if __name__=='__main__':
    unittest.main()
