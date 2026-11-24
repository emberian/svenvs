# Run with perl -0777 -p. Keep line numbers and quoted strings, since SML
# generators can include literal comment delimiters in the code they emit.
s{
    ("(?:[^"\\]++|\\.)*+")                  # quoted string
  | (?<comment>
        \(\*
        (?: [^(*]++ | \((?!\*) | \*(?!\)) | (?&comment) )*+
        \*\)
    )
}{
    defined $1 ? $1 : ($+{comment} =~ s/[^\n]/ /gr)
}gsxe;
