![Verified Software Toolchain](chain.jpg)

## Fusion: exact stores and overlapping integer views

This branch extends **VST 2.16** to verify code that writes a wide integer and
then reads an overlapping narrower view, such as a 64-bit union member followed
by a 32-bit member. Ordinary VST `mapsto` describes a decoded value; it does not
always determine the exact stored representation needed to justify that narrower
read. Fusion preserves this information **at the store**, then exposes readable
views while retaining ownership of the complete object.

The extensions currently provide:

- **Optional exact stores in the same sealed Floyd logic**: `exact_mapsto`, the
  soundness-backed `semax_store_exact` rule, and a ramification wrapper for a
  selected SEP entry. Proofs continue to use ordinary `semax_body`, calls and VSU
  composition; ordinary store behavior is preserved.
- **Reusable memory and integer views**: installed `FusionMemvals` and
  `FusionViews64` modules provide prefix borrowing, low/high 32-bit views of a
  64-bit integer on little-endian targets, wide read-back, and split/reassembly.
  `FusionStore` exports these APIs; application proofs supply their layout,
  alignment and ownership conditions.
- **Normal VST build and installation**: implementation modules live in
  [`floyd/`](floyd/), with regression examples in
  [`progs64/fusion/`](progs64/fusion/). Standard Make/opam builds and installed-client
  checks cover ordinary/exact stores, caller/main, VSU, overlapping views and the
  representation counterexample, together with assumption audits and `coqchk`.

**Start with [the Fusion API and build guide](doc/fusion.md)**: module structure
(§2), theorem signatures and prerequisites (§3–4), proof composition and the
representation distinction (§5), installation/update (§6), and tests (§7).
The maintained branch is **`fusion/vst-2.16`**, with one complete public interface.
The currently validated environment is x86-64 little-endian, Rocq 9.0.0 and
CompCert 3.17.

### Typed exact layer development

The next typed ownership interface is being developed on **`fusion/vst-2.16-dev`**.
See [the development design and prototypes](doc/design/typed-exact/README.md).
This work is not yet a released API; **`fusion/vst-2.16`** remains the consumer
upstream and receives the feature only after implementation and validation are complete.

## Upstream VST

With contributions from

[Andrew W. Appel](http://www.cs.princeton.edu/~appel/),
[Lennart Beringer](http://www.cs.princeton.edu/~eberinge/),
[Robert Dockins](http://rwd.rdockins.name/),
[Josiah Dodds](http://www.cs.princeton.edu/~jdodds/),
[Aquinas Hobor](http://www.comp.nus.edu.sg/~hobor/),
[Jean-Marie Madiot](https://madiot.fr/),
[Gordon Stewart](http://www.cs.princeton.edu/~jsseven/),
[Qinxiang Cao](http://jhc.sjtu.edu.cn/people/members/faculty/qinxiang-cao.html),
Qinshi Wang,
and others.

The [LICENSE](LICENSE) file has information about copyright, licensing, and permissions.

## How to install:

For this Fusion branch, follow [the standard opam instructions in the Fusion guide](doc/fusion.md).
For general VST build options, see [BUILD_ORGANIZATION.md](BUILD_ORGANIZATION.md).

## Documentation:

[Our webpage](https://vst.cs.princeton.edu) describes the goals of the project
and has links to many related publications.

For an introduction to how to use Verifiable C,
[read the manual](doc/VC.pdf),
or consult [Software Foundations Volume 5: Verifiable C](https://softwarefoundations.cis.upenn.edu/vc-current/index.html)
for a tutorial with exercises.

[Program Logics for Certified Compilers](https://www.cs.princeton.edu/~appel/papers/plcc.pdf), by Andrew W. Appel et al.,
Cambridge University Press, 2014.
Available in [hardcover](https://www.barnesandnoble.com/w/program-logics-for-certified-compilers-andrew-w-appel/1126363773).
