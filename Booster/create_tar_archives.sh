#!/bin/bash

base_dir="/home/sangjune/data1/regression/gen_tests/defects4j_2.0.1/BaseDevTests2_filtered"

echo "================================================================"
echo "     CREATING TAR ARCHIVES FROM FILTERED TEST FILES            "
echo "================================================================"
echo "Base directory: $base_dir"
echo ""

if [[ ! -d "$base_dir" ]]; then
  echo "Error: Base directory not found: $base_dir"
  exit 1
fi

total_created=0
total_removed=0
total_failed=0

# 모든 프로젝트 순회
for project_dir in "$base_dir"/*; do
  if [[ ! -d "$project_dir" ]]; then
    continue
  fi
  
  project_name=$(basename "$project_dir")
  tar_extracted_dir="$project_dir/tar_extracted"
  
  if [[ ! -d "$tar_extracted_dir" ]]; then
    echo "⊝ No tar_extracted directory for $project_name (skipping)"
    continue
  fi
  
  echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  echo "Processing project: $project_name"
  echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  
  # tar_extracted 안의 각 버그 버전 순회
  for bug_dir in "$tar_extracted_dir"/*; do
    if [[ ! -d "$bug_dir" ]]; then
      continue
    fi
    
    bug_version=$(basename "$bug_dir")
    tar_output_dir="$project_dir/tar/$bug_version"
    tar_filename="${project_name}-${bug_version}-dev.tar.bz2"
    tar_output_path="$tar_output_dir/$tar_filename"
    
    # tar 출력 디렉토리 생성
    if [[ ! -d "$tar_output_dir" ]]; then
      mkdir -p "$tar_output_dir"
    fi
    
    # 이미 tar 파일이 존재하면 삭제
    if [[ -f "$tar_output_path" ]]; then
      rm -f "$tar_output_path"
      total_removed=$((total_removed + 1))
    fi
    
    # tar.bz2 생성
    # tar_extracted/1b/ 안의 내용을 압축 (디렉토리 자체가 아닌 내용만)
    pushd "$bug_dir" > /dev/null
    
    # .java 파일이나 .txt 파일이 있는지 확인
    file_count=$(find . -type f \( -name "*.java" -o -name "*.txt" \) | wc -l)
    
    if [[ $file_count -eq 0 ]]; then
      echo "  ⊝ No files to archive: $project_name/$bug_version"
      popd > /dev/null
      continue
    fi
    
    # tar.bz2 생성
    tar -cjf "$tar_output_path" . 2>/dev/null
    
    if [[ $? -eq 0 ]]; then
      tar_size=$(du -h "$tar_output_path" | cut -f1)
      echo "  ✓ Created: $project_name/$bug_version ($tar_size, $file_count files)"
      total_created=$((total_created + 1))
    else
      echo "  ✗ Failed: $project_name/$bug_version"
      total_failed=$((total_failed + 1))
    fi
    
    popd > /dev/null
  done
  
  echo ""
done

echo "================================================================"
echo "                    ARCHIVE CREATION SUMMARY                   "
echo "================================================================"
echo " Old archives removed: $total_removed"
echo " Archives created:     $total_created"
echo " Failed:               $total_failed"
echo "================================================================"
