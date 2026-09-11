#!/bin/bash

if [ "$KEMS_HOME" = "" ] ; then
  echo "ERROR: KEMS_HOME environment variable must be set!"
  exit 1
fi

if [ "$1" = "" ] ; then
  echo "ERROR: You must provide a sequence name as first argument "
  echo "Usage: executeIPLSequence.sh <sequence> <results_file>"
  echo "<sequence> is the name of the file where the prover sequence is"
  echo "<results_file> is the name of the file where the result are going to be written"
  exit 1
fi

if [ "$2" = "" ] ; then
  echo "ERROR: You must provide a file name as second argument "
  echo "Usage: executeIPLSequence.sh <sequence> <results_file>"
  echo "<sequence> is the name of the file where the prover sequence is"
  echo "<results_file> is the name of the file where the result are going to be written"
  exit 1
fi

# Change to kems.export directory from the current working directory
cd $KEMS_HOME/kems.export
echo "Executing IPL sequence $1"
echo "Saving in results file $2"
echo "Using IPL-specific configuration..."

# Use the compiled classes from kems.prover and include all necessary jars
java -Xms200m -Xmx800m -cp "$KEMS_HOME/kems.prover/bin:$KEMS_HOME/kems.export/lib/generated/ipl.jar:$KEMS_HOME/kems.export/lib/ext/*:$KEMS_HOME/kems.export/lib/generated/*" proverinterface.ProverInterface $KEMS_HOME/kems.tests/$1 | tee $KEMS_HOME/kems.tests/$2
