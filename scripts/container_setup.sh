#!/usr/bin/env bash
# MergeXO executes this standalone script as root before the repository checkout.
set -euo pipefail

case "$(uname -s)/$(uname -m)" in
  Linux/x86_64)
    arch=x64
    jdk_sha=8b9b611d917e3dfd8419d3566b5949226f69b052fed7e109c1368add1dfe8711
    ;;
  Linux/aarch64)
    arch=aarch64
    jdk_sha=3e4eca7ead088f080af1476007decf010a240a1eb4e1e78c54fa32fbcc347084
    ;;
  *) echo "Container setup supports Linux amd64/arm64" >&2; exit 1 ;;
esac

staging_dir="$(mktemp -d)"
trap 'rm -rf "$staging_dir"' EXIT

# Match CI's Temurin 17 JDK; pin the archive and checksum for reproducibility.
curl --fail --location --retry 3 --output "$staging_dir/jdk.tar.gz" \
  "https://github.com/adoptium/temurin17-binaries/releases/download/jdk-17.0.21%2B9/OpenJDK17U-jdk_${arch}_linux_hotspot_17.0.21_9.tar.gz"
printf '%s  %s\n' "$jdk_sha" "$staging_dir/jdk.tar.gz" | sha256sum --check --status
mkdir -p /opt/mergexo-jdk
tar -xzf "$staging_dir/jdk.tar.gz" -C /opt/mergexo-jdk --strip-components=1
# Exports in setup cannot change the parent worker: install commands on its PATH.
for binary in /opt/mergexo-jdk/bin/*; do
  ln -sf "$binary" "/usr/local/bin/${binary##*/}"
done
java -version

# Official launcher; the checked-out project/build.properties selects sbt.
curl --fail --location --retry 3 --output "$staging_dir/sbt.tgz" \
  "https://github.com/sbt/sbt/releases/download/v1.11.2/sbt-1.11.2.tgz"
printf '%s  %s\n' 84c7b9d8e20c5dc8356154a5b7146c0a8b86aba97268ce9fe1a585d2c8908f4f "$staging_dir/sbt.tgz" | sha256sum --check --status
mkdir -p /opt/mergexo-sbt
tar -xzf "$staging_dir/sbt.tgz" -C /opt/mergexo-sbt --strip-components=1
ln -sf /opt/mergexo-sbt/bin/sbt /usr/local/bin/sbt

# Match CI's Node 22, including npm, for Scala.js and browser tooling.
case "$arch" in
  x64)
    node_arch=x64
    node_sha=1805bcd35e6815559bd2eb97db438d3fdb0eb3a5e6a977b7c1badca76337e9ce
    ;;
  aarch64)
    node_arch=arm64
    node_sha=6287aa46b6c375d816e63ae66d024fbbfd70404825aabdfdf898a970871d2f4b
    ;;
esac
curl --fail --location --retry 3 --output "$staging_dir/node.tar.xz" \
  "https://nodejs.org/dist/v22.23.4/node-v22.23.4-linux-${node_arch}.tar.xz"
printf '%s  %s\n' "$node_sha" "$staging_dir/node.tar.xz" | sha256sum --check --status
mkdir -p /opt/mergexo-node
tar -xJf "$staging_dir/node.tar.xz" -C /opt/mergexo-node --strip-components=1
for binary in node npm npx; do
  ln -sf "/opt/mergexo-node/bin/$binary" "/usr/local/bin/$binary"
done
node --version

# The Bookworm worker's GCC 12 lacks C++20 <format>, required by current Z3.
# Debian supplies LLVM 19 and libc++ without adding a third-party package source.
apt-get update
DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
  clang-19 llvm-19 libc++-19-dev libc++abi-19-dev \
  cmake ninja-build python3 file patch
rm -rf /var/lib/apt/lists/*

# Persist the compiler selection for both CMake and Scala Native after setup exits.
ln -sf /usr/bin/clang-19 /usr/local/bin/clang
ln -sf clang /usr/local/bin/cc
ln -sf /usr/bin/llvm-config-19 /usr/local/bin/llvm-config
cat > "$staging_dir/clang++" <<'COMPILER'
#!/usr/bin/env bash
exec /usr/bin/clang++-19 -stdlib=libc++ "$@"
COMPILER
install -m 755 "$staging_dir/clang++" /usr/local/bin/clang++
ln -sf clang++ /usr/local/bin/c++
clang --version

# Fail during setup, before the long Z3 builds, if the C++ library is unsuitable.
cat > "$staging_dir/format.cpp" <<'CPP'
#include <format>
int main() { return std::format("{}", 42) != "42"; }
CPP
c++ -std=c++20 "$staging_dir/format.cpp" -o "$staging_dir/format"
"$staging_dir/format"
