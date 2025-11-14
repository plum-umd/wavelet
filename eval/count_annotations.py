#!/usr/bin/env python3
"""
Count capability annotations (#[cap(...)] and fence! macros in eval/src files.
"""

import os
import re
from pathlib import Path

def count_annotations(file_path):
    """Count capability annotations, fence! macros, and source lines in a file."""
    cap_count = 0
    fence_count = 0
    source_lines = 0
    
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            for line in f:
                stripped = line.strip()
                
                # Skip empty lines
                if not stripped:
                    continue
                
                # Check for cap and fence
                has_cap = re.search(r'#\[cap\(', line)
                has_fence = re.search(r'fence!\s*\(', line)
                
                if has_cap:
                    cap_count += 1
                elif has_fence:
                    fence_count += 1
                else:
                    # Count as source line (non-empty, not cap, not fence)
                    source_lines += 1
    except Exception as e:
        print(f"Error reading {file_path}: {e}")
        return None, None, None
    
    return cap_count, fence_count, source_lines

def main():
    # Get the eval/src directory
    script_dir = Path(__file__).parent
    src_dir = script_dir / "src"
    
    if not src_dir.exists():
        print(f"Error: Directory {src_dir} not found")
        return
    
    # Collect all .rs files
    rs_files = sorted(src_dir.glob("*.rs"))
    
    if not rs_files:
        print(f"No .rs files found in {src_dir}")
        return
    
    # filter main.rs, dconv.rs, fft.rs
    rs_files = [f for f in rs_files if f.name not in {"main.rs", "dconv.rs", "fft.rs"}]
    if not rs_files:
        print(f"No relevant .rs files found in {src_dir} after filtering")
        return
    
    # Store results
    results = []
    total_cap = 0
    total_fence = 0
    total_source = 0
    
    # Process each file
    for file_path in rs_files:
        cap_count, fence_count, source_count = count_annotations(file_path)
        if cap_count is not None:
            results.append((file_path.name, cap_count, fence_count, source_count))
            total_cap += cap_count
            total_fence += fence_count
            total_source += source_count
    
    # Print header
    print("\n" + "="*90)
    print("Capability Annotations, fence! Macros, and Source Line Statistics")
    print("="*90)
    # print(f"{'File':<20} {'#[cap(...)]':>12} {'fence!()':>12} {'Source':>12} {'Total':>12} {'Cap%':>8}")
    print(f"{'File':<20} {'#[cap(...)]':>12} {'fence!()':>12} {'Source':>12} {'Total':>12} ")
    print("-"*90)
    
    # Print each file's results
    for filename, cap_count, fence_count, source_count in results:
        total = cap_count + fence_count + source_count
        cap_percentage = (cap_count / total * 100) if total > 0 else 0
        print(f"{filename:<20} {cap_count:>12} {fence_count:>12} {source_count:>12} {total:>12} ")
    
    # Print totals
    print("-"*90)
    grand_total = total_cap + total_fence + total_source
    total_cap_percentage = (total_cap / grand_total * 100) if grand_total > 0 else 0
    print(f"{'TOTAL':<20} {total_cap:>12} {total_fence:>12} {total_source:>12} {grand_total:>12} {total_cap_percentage:>7.1f}%")
    print("="*90)
    
    # Print summary
    print(f"\nSummary:")
    print(f"  Total files processed: {len(results)}")
    print(f"  Total #[cap(...)] annotations: {total_cap}")
    print(f"  Total fence!() macros: {total_fence}")
    print(f"  Total source lines (non-empty): {total_source}")
    print(f"  Grand total lines: {grand_total}")
    print(f"  Capability annotation ratio: {total_cap_percentage:.1f}%")
    
    # Print files with most annotations
    if results:
        print(f"\nTop files by annotation count:")
        sorted_results = sorted(results, key=lambda x: x[1], reverse=True)
        for i, (filename, cap_count, fence_count, source_count) in enumerate(sorted_results[:5], 1):
            total = cap_count + fence_count + source_count
            cap_pct = (cap_count / total * 100) if total > 0 else 0
            print(f"  {i}. {filename}: {cap_count} cap annotations ({cap_pct:.1f}% of {total} lines)")
    
    print()

if __name__ == "__main__":
    main()
