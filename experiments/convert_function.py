import os
import re
import json

def extract_info_from_file(file_path):
    with open(file_path, 'r', encoding='utf-8') as file:
        content = file.read()

    nodes = re.findall(r'Nodes:([\s\S]*?)(?=Properties:|$)', content)
    properties = re.findall(r'Properties:([\s\S]*?)(?=Potential triples:|$)', content)
    potential_triples = re.findall(r'Potential triples:([\s\S]*?)(?=Nodes:|$)', content)

    nodes = nodes[0].strip().split('\n') if nodes else []
    properties = properties[0].strip().split('\n') if properties else []
    potential_triples = potential_triples[0].strip().split('\n') if potential_triples else []

    return {
        'Nodes': [line.strip() for line in nodes if line.strip()],
        'Properties': [line.strip() for line in properties if line.strip()],
        'Potential triples': [line.strip() for line in potential_triples if line.strip()]
    }

def main():
    base_dir = 'Data/ontology'
    output = {}

    for root, dirs, files in os.walk(base_dir):
        for file in files:
            if file.endswith('.txt'):
                file_path = os.path.join(root, file)
                file_info = extract_info_from_file(file_path)
                output[file] = file_info

    with open('output.json', 'w', encoding='utf-8') as json_file:
        json.dump(output, json_file, indent=4)

if __name__ == "__main__":
    main()