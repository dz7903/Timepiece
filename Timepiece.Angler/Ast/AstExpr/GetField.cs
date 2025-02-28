using Newtonsoft.Json;

namespace Timepiece.Angler.Ast.AstExpr;

public record GetField : Expr
{
  public GetField(Type recordTy, Type fieldTy, Expr record, string fieldName)
  {
    Record = record;
    FieldName = fieldName;
    RecordType = recordTy;
    FieldType = fieldTy;
  }

  [JsonConstructor]
  public GetField(string recordType, string fieldType, Expr record, string fieldName) : this(
    TypeParsing.ParseType(recordType).MakeType(), TypeParsing.ParseType(fieldType).MakeType(), record, fieldName)
  {
  }

  public Expr Record { get; set; }
  public string FieldName { get; set; }
  public Type RecordType { get; set; }
  public Type FieldType { get; set; }

  public override void Rename(string oldVar, string newVar)
  {
    Record.Rename(oldVar, newVar);
  }
}
