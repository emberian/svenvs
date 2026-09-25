"""
Plumbing shared by the closed-loop demos: talk to a svenvs Candle
place-server (scripts/place-server.sh) running on some host you reach over
ssh. Nothing about any particular machine is baked in; it all comes from the
environment:

  SVENVS_CANDLE_HOST         ssh destination running the server: an alias
                             from your ssh config, or user@host. REQUIRED for
                             the live-kernel path; when unset the demos say so
                             and take their loud DEGRADED local-mirror path.
  SVENVS_CANDLE_SSH_KEY      optional identity file (default: whatever your
                             ssh config / agent provides for that host)
  SVENVS_CANDLE_REMOTE_ROOT  a svenvs checkout on that host; its
                             scripts/place-submit.sh drives the server
                             (default: ~/svenvs)
  SVENVS_CANDLE_PLACE_DIR    the server's PLACE_DIR on that host, only if it
                             was started with a non-default one
  SVENVS_CANDLE_TIMEOUT      seconds to wait for one submission (default 180)

Every call is one short, timed ssh (the place-server rule: light submissions
only). The obligation text travels on the ssh's stdin into a mktemp file that
is removed after the submission, so nothing predictable is left in a shared
temp directory on either side.
"""
import os
import re
import shlex
import subprocess

_ANSI = re.compile(r"\x1b\[[0-9;]*m")


class RemoteCandle:
    HOWTO = ("set SVENVS_CANDLE_HOST=<ssh destination> to a host running "
             "scripts/place-server.sh from a svenvs checkout "
             "(SVENVS_CANDLE_REMOTE_ROOT, default ~/svenvs); "
             "see agent/closedloop/README.md")

    def __init__(self, env=None):
        env = os.environ if env is None else env
        self.host = env.get("SVENVS_CANDLE_HOST") or None
        self.key = env.get("SVENVS_CANDLE_SSH_KEY") or None
        root = env.get("SVENVS_CANDLE_REMOTE_ROOT") or "~/svenvs"
        # a leading ~ must expand on the REMOTE side: hand it over as $HOME
        self.root = "$HOME" + root[1:] if root.startswith("~") else root
        self.place_dir = env.get("SVENVS_CANDLE_PLACE_DIR") or None
        self.timeout = int(env.get("SVENVS_CANDLE_TIMEOUT") or 180)

    @property
    def configured(self):
        return self.host is not None

    def describe(self):
        where = f"{self.host}:{self.root}"
        return where + (f" (PLACE_DIR={self.place_dir})" if self.place_dir else "")

    # ---- one ssh, always bounded ------------------------------------------
    def _ssh(self, remote_cmd, stdin=None, timeout=None):
        args = ["ssh", "-o", "ConnectTimeout=10", "-o", "BatchMode=yes"]
        if self.key:
            args += ["-i", os.path.expanduser(self.key)]
        args += [self.host, remote_cmd]
        return subprocess.run(args, input=stdin, capture_output=True,
                              text=True, timeout=timeout or self.timeout)

    def _script(self, name):
        pre = f"PLACE_DIR={shlex.quote(self.place_dir)} " if self.place_dir else ""
        return f'{pre}bash "{self.root}/scripts/{name}"'

    # ---- the two operations the demos need --------------------------------
    def alive(self):
        """True iff a place-server is up on the host (its --status probe)."""
        try:
            r = self._ssh(self._script("place-server.sh") + " --status",
                          timeout=20)
            return r.returncode == 0
        except Exception:
            return False

    def submit(self, body, sentinel):
        """Feed `body` (HOL Light text) to the live kernel and wait until it
        echoes `sentinel`. Returns the kernel's own output for this submission
        (the log slice place-submit.sh prints), or None on any failure."""
        cmd = ('f="$(mktemp "${TMPDIR:-/tmp}/svenvs-submit.XXXXXX")" && '
               'cat > "$f" && ' + self._script("place-submit.sh")
               + f' "$f" {shlex.quote(sentinel)}; rc=$?; rm -f "$f"; exit $rc')
        try:
            r = self._ssh(cmd, stdin=body)
        except (subprocess.TimeoutExpired, OSError):
            return None
        if r.returncode != 0:
            return None
        return _ANSI.sub("", r.stdout)     # the kernel colours its echoes
