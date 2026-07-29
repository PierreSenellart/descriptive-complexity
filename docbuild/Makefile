DOCOUT   = .lake/build/doc
DOCS_URL = https://pierresenellart.github.io/descriptive-complexity

# Per-declaration dependency figures, from result-graph. Entirely optional: if
# the binary is not built, `make docs` produces exactly what it did before.
# Point RESULT_GRAPH_REPO elsewhere if your checkout is not a sibling of this one.
RESULT_GRAPH_REPO ?= ../../result-graph
RESULT_GRAPH      := $(abspath $(RESULT_GRAPH_REPO)/.lake/build/bin/result-graph)
RG_INJECT         := $(abspath $(RESULT_GRAPH_REPO)/scripts/inject-docs.py)
RG_CSS            := $(abspath $(RESULT_GRAPH_REPO)/scripts/result-graph.css)
RG_OUT            := .lake/build/result-graph
LEAN_SOURCES      := $(shell find .. -name '*.lean' -not -path '../.lake/*' \
                       -not -path '../docbuild/*')

docs: graphs
	# Force a fresh HTML stitching step: `lake build DescriptiveComplexity:docs`
	# can otherwise reuse a stale "library built" marker that pre-dates a newly
	# added module (the underlying .olean/docInfo artifacts are still cached, so
	# the cost is just the final fromDb HTML pass).
	rm -f .lake/build/doc-data/DescriptiveComplexity--library.docs_built
	# Same for the bibliography prepass, for a sharper reason: the output Lake
	# tracks for it sits in doc-data/, but the files it emits – doc/references.bib
	# and doc/declarations/references.json – sit under doc/. Carry doc-data/ over
	# without doc/, as CI does when it caches the database alone, and Lake finds
	# the prepass up to date while its real outputs are absent, so the final
	# fromDb pass dies on a missing doc/references.bib. Re-running it is cheap.
	rm -f .lake/build/doc-data/references.json
	lake build DescriptiveComplexity:docs
	# Dependency figure at the foot of each declaration, folded away by
	# default. Idempotent, and skipped entirely when result-graph is absent,
	# so this cannot break a docs build. Undo with `make ungraph`.
	@if [ -d "$(RG_OUT)/svg" ]; then \
	  grep -q 'details.result-graph' $(DOCOUT)/style.css \
	    || cat "$(RG_CSS)" >> $(DOCOUT)/style.css; \
	  "$(RG_INJECT)" --doc $(DOCOUT) --graphs $(RG_OUT)/svg; \
	else \
	  echo "note: no figures in $(RG_OUT)/svg – skipping"; \
	fi

# The graph of the whole library. Importing Mathlib is the slow part, so it is
# redone only when a source file, or result-graph itself, changed. The
# $(wildcard) is what makes the whole feature optional: with no result-graph
# checkout there is simply no prerequisite, and the guard below turns the
# recipe into a no-op.
$(RG_OUT)/deps.json: $(LEAN_SOURCES) $(wildcard $(RESULT_GRAPH))
	@if [ ! -x "$(RESULT_GRAPH)" ]; then \
	  echo "note: no result-graph at $(RESULT_GRAPH) – skipping dependency figures"; \
	  exit 0; \
	fi; \
	set -e; mkdir -p $(RG_OUT); \
	cd .. && LEAN_PATH="$$(find .lake -type d -path '*/build/lib/lean' | tr '\n' ':')" \
	  "$(RESULT_GRAPH)" --root DescriptiveComplexity --json docbuild/$@ --stats

# One figure per declaration. `dot` runs once per declaration, so this is the
# expensive step: about two minutes and 86 MB of SVG for this library's 4,648
# declarations. Radius 2 keeps the figures small (median 10 nodes, 4% over the
# node cap). Cleaned first, or declarations you deleted leave orphan SVGs.
$(RG_OUT)/svg: $(RG_OUT)/deps.json
	@if [ ! -f "$<" ]; then exit 0; fi; \
	set -e; rm -rf $@; \
	"$(RESULT_GRAPH)" --from-json $< --all $@ --render \
	  --depth 2 --dir uses --reduce --url-base $(DOCS_URL); \
	touch $@

graphs: $(RG_OUT)/svg

ungraph:
	"$(RG_INJECT)" --doc $(DOCOUT) --remove

.PHONY: docs graphs ungraph
