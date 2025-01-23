from data_loader import load_data
from prompt_generator import load_ontology, generate_prompt
from model_interface import LLMModel
from score_function import calculate_score
import argparse



def main(train_data_path, test_data_path, ontology_path, model_path):

    
    train_data = load_data(train_data_path)
    test_data = load_data(test_data_path)
    ontology = load_ontology(ontology_path)
    prompt = generate_prompt(train_data, ontology)
    
    model = LLMModel(model_path)  # Initialize with your actual LLM API
    output_file = open('output.txt', 'w')
    for data in test_data:
        prompt_test = prompt + "Table: " + data["table"] + "\n"
        prompt_test = prompt_test + "The semantic graph of the table in the strict format of given examples above: "
        semantics = model.get_semantics(prompt)
        output_file.write(semantics)
        # score = calculate_score(semantics, data["semantic_graph"])
        # output_file.write("Score: " + str(score))
    output_file.close()

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--train_data_path", type=str, required=True)
    parser.add_argument("--test_data_path", type=str, required=True)
    parser.add_argument("--ontology_path", type=str, required=True)
    parser.add_argument("--model_path", type=str, required=True)
    args = parser.parse_args()
    main(args.train_data_path, args.test_data_path, args.ontology_path, args.model_path)