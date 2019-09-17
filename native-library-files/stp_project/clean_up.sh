#/usr/bin/env/ bash

# Clean up the build files for StpJavaApi
# cryptominisat repo is also removed

set -e

# remove STP repo
#[ -d "./stp" ] && rm -rf ./stp ||:


# the built STP library should have been copied out 
[ -d "./stpJ/build" ] && rm -rf ./stpJ/build ||:

DESTN_DIR=$PWD/stpJ/install_include
[ ! -f "$DESTN_DIR" ] && rm -rf "$DESTN_DIR"/* ||:

#remove cryptominisat repo
[ -d "./dependencies/cryptominisat" ] && rm -rf ./dependencies/cryptominisat ||:

# java builds

echo "Build files and cloned repos removed."
