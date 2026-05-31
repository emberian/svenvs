# Thin wrapper around build.sh so `make` in this directory reproduces the
# release artifact. The real logic (pinned compiler, sha256, link steps)
# lives in build.sh, which is also what CI runs.

OUTDIR ?= _build
BIN     = $(OUTDIR)/envelope_console

.PHONY: all run clean

all: $(BIN)

$(BIN): envelope_console.cml build.sh
	./build.sh $(OUTDIR)

run: $(BIN)
	$(BIN)

clean:
	rm -rf $(OUTDIR)
