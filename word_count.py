#!/usr/bin/env python3
import subprocess
import json
COQWC = "coqwc"
COQPROJECT_FILES_PATH = "file_categories.txt"
KEYWORDS = ["Theorem", "Lemma", "Fact", "Remark", "Corollary", "Proposition", "Property"]

def coq_wc_get(filepath):
    output = subprocess.Popen([COQWC, filepath],stdout=subprocess.PIPE)
    return output.stdout.read()

def count_keywords(filepath):
    count = 0
    with open(filepath) as f:
        for l in f:
            words = l.strip().split()
            if len(words) > 0 and words[0] in KEYWORDS:
                count += 1
    return count

def coq_file_get_stats(filepath):
    lines = coq_wc_get(filepath).splitlines()
    cats = lines[0].strip().split()
    vals = lines[1].strip().split()

    valdict = dict()
    for c,v in zip(cats,vals) :
        valdict[c.decode('UTF-8')] = int(v)

    #add the number of KEYWORD appearances to the dict
    valdict["#Lemma"] = count_keywords(filepath)

    return valdict

def mergeDictionary(dict_1, dict_2):
   dict_3 = {**dict_1, **dict_2}
   for key, value in dict_3.items():
       if key in dict_1 and key in dict_2:
               dict_3[key] = value + dict_1[key]
   return dict_3

def combine_counts(file1_dict,file2_dict):
    return mergeDictionary(file1_dict,file2_dict)

def coqproject_parse(cp_file):
    cur_category = ""
    file_categories = {}
    for line in cp_file:
        line = line.strip()
        if line.startswith("#") or line == "":
            pass
        elif line.startswith("@"):
            cur_category = line[1:]
            file_categories[cur_category] = []
        else:
            ##TODO: add filters for sections/Lemmas
            if cur_category:
                file_categories[cur_category] += [line]
    return file_categories

def measure_files_as_dict(files):
    file_dicts = [coq_file_get_stats(f) for f in files]
    acc_dict = dict()
    [acc_dict := combine_counts(d,acc_dict) for d in file_dicts]
    return acc_dict

def measure_cerise():
    measurements = dict()
    with open(COQPROJECT_FILES_PATH) as f:
        files_dict = coqproject_parse(f)
        for cat,files in files_dict.items():
            measurements[cat] = measure_files_as_dict(files)
    return measurements

def main():
    print(json.dumps(measure_cerise(),\
                     sort_keys=True, indent=4))

if __name__ == "__main__":
    main()
