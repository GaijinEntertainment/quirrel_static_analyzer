find . -name "*.nut" > ~nuts.tmp

../../../../../tools/dagor3_cdk/util-linux64/sq3_static_analyzer-dev \
  --csq-exe:../../../../../tools/dagor3_cdk/util-linux64/csq-dev \
  --files:~nuts.tmp --output:analysis_log.txt

if [ $? -eq 0 ]
then
  echo "OK"
else
  echo "FAIL"
fi

rm ~nuts.tmp
