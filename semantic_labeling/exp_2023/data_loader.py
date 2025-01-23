import os
import json
import random
import chardet


def detect_encoding(file_path):
    with open(file_path, 'rb') as file:
        raw_data = file.read()
    result = chardet.detect(raw_data)
    return result['encoding']


def load_data(file_path, size=0):
    """Load table data from a file."""
    with open(file_path, 'r', encoding=detect_encoding(file_path)) as file:
        data = json.load(file)


    # idx = 0
    # result = []
    # if size > 0:
    #     while count < size:
    #         if not check_data_empty(data[idx]):
    #             count += 1
    #             result.append(data[count])
    #         idx += 1
    #     return result
    # else:
    #     return data
    if size > 0:
        data = data[: size]
        for entry in data:
            for key, value in entry.items():
                if value is None or len(str(value)) < 1 or value == "\n":  # Check for null values
                    entry[key] = "<Empty>"  # Replace null with <Empty>
    return data

def load_ontologies(file_path):
    """Load ontologies from a JSON file."""
    with open(file_path, 'r', encoding='utf-8') as file:
        ontologies = json.load(file)
    return ontologies

def check_data_empty(data):
    for key, value in data.items():
        if value is None or len(str(value)) < 1:
            return True
    return False
    
def generate_data(sources_dir, models_dir, num_files=0, size=0, test_size=0.2, random_state= None):
    """Load training input and output data from specified directories."""
    source_files = sorted(os.listdir(sources_dir))
    model_files = sorted(os.listdir(models_dir))
    

    
    # Create a list of indices and shuffle it
    indices = list(range(len(source_files)))
    if random_state is not None:
      random.seed(random_state)
      random.shuffle(indices)

    if num_files > 0:
      indices = indices[:num_files]

    
    # Use the shuffled indices to reorder source_files and model_files
    source_files = [source_files[i] for i in indices]
    model_files = [model_files[i] for i in indices]
    
    # Split into training and test sets based on indices
    split_index = int(len(indices) * (1 - test_size))
    train_indices = list(range(split_index))
    test_indices = list(range(split_index, len(indices)))
    
    def load_data_tuples(indices):
        print(f"Loading data from {indices} files")
        data_tuples = []
        for idx in indices:
            source_file = source_files[idx]
            model_file = model_files[idx]
            source_file_path = os.path.join(sources_dir, source_file)
            model_file_path = os.path.join(models_dir, model_file)
            print(f"Loading data from {source_file_path} and {model_file_path}")
            
            input_data = load_data(source_file_path, size)
            output_data = load_data(model_file_path)
            data_tuples.append({"table":input_data, "semantic_graph":output_data})
        return data_tuples
    
    train_data_tuples = load_data_tuples(train_indices)
    test_data_tuples = load_data_tuples(test_indices)
    
    return train_data_tuples, test_data_tuples