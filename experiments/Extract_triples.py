import os
import yaml
import json

global nodes
nodes = []
global links
links = []
global attributes
attributes = []
global types
types = []


def extract_triples(data):
    semantic_triples = []
    internal_link_triples = []
    for command in data.get('commands', []):
        if command['_type_'] == 'SetSemanticType':
            triple = (command['node_id'], command['type'], command['input_attr_path'])
            semantic_triples.append(triple)
            nodes.append(command['node_id'])
            attributes.append(command['input_attr_path'])
            types.append(command['type'])
        elif command['_type_'] == 'SetInternalLink':
            triple = (command['source_id'], command['link_lbl'], command['target_id'])
            internal_link_triples.append(triple)
            links.append(command['link_lbl'])
            nodes.append(command['source_id'])
            nodes.append(command['target_id'])  
    return semantic_triples, internal_link_triples

def process_yaml_files(folder_path, output_folder_path):
    for filename in os.listdir(folder_path):
        if filename.endswith('.yml') or filename.endswith('.yaml'):
            file_path = os.path.join(folder_path, filename)
            with open(file_path, 'r') as file:
                data = yaml.safe_load(file)
                semantic_triples, internal_link_triples = extract_triples(data)
                # Create an output file using the original file name without extension
                output_file = os.path.splitext(filename)[0] + '.json'
                output_path = os.path.join(output_folder_path, output_file)
                with open(output_path, 'w') as outfile:
                    json.dump({
                        'semantic_triples': semantic_triples,
                        'internal_link_triples': internal_link_triples
                    }, outfile, indent=4)

def main():
    folder_path = 'Data/models-y2rml/'
    output_path = 'Data/models-triples/'
    output_nodes_path = 'Data/models-nodes.txt'
    output_links_path = 'Data/models-links.txt'
    output_attributes_path = 'Data/models-attributes.txt'
    output_types_path = 'Data/models-types.txt'
    process_yaml_files(folder_path, output_path)
    with open(output_nodes_path, 'w') as outfile:
        for node in nodes:
            outfile.write(f"{node}\n")
    with open(output_links_path, 'w') as outfile:
        for link in links:
            outfile.write(f"{link}\n")
    with open(output_attributes_path, 'w') as outfile:
        for attribute in attributes:
            outfile.write(f"{attribute}\n")
    with open(output_types_path, 'w') as outfile:
        for t in types:
            outfile.write(f"{t}\n")

if __name__ == "__main__":
    main()